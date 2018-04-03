// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/tapirstore/shardclient.cc:
 *   Single shard tapir transactional client.
 *
 * Copyright 2015 Irene Zhang <iyzhang@cs.washington.edu>
 *                Naveen Kr. Sharma <naveenks@cs.washington.edu>
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 **********************************************************************/

#include "store/tapirstore/shardclient.h"

namespace tapirstore {

using namespace std;
using namespace proto;

ShardClient::ShardClient(const string &configPath,
                       Transport *transport, uint64_t client_id, int
                       shard, int closestReplica)
    : client_id(client_id), transport(transport), shard(shard)
{
    ifstream configStream(configPath);
    if (configStream.fail()) {
        Panic("Unable to read configuration file: %s\n", configPath.c_str());
    }

    transport::Configuration config(configStream);
    this->config = &config;

    client = new replication::ir::IRClient(config, transport, client_id);

    if (closestReplica == -1) {
        replica = client_id % config.n;
    } else {
        replica = closestReplica;
    }
    Debug("Sending unlogged to replica %i", replica);

    waiting = NULL;
    blockingBegin = NULL;
}

ShardClient::~ShardClient()
{
    delete client;
}

void
ShardClient::Begin(uint64_t id)
{
    Debug("[shard %i] BEGIN: %lu", shard, id);

    // Wait for any previous pending requests.
    if (blockingBegin != NULL) {
        blockingBegin->GetReply();
        delete blockingBegin;
        blockingBegin = NULL;
    }
}

void
ShardClient::Get(uint64_t id, const string &key, Promise *promise)
{
    // Send the GET operation to appropriate shard.
    Debug("[shard %i] Sending GET [%lu : %s]", shard, id, key.c_str());

    // create request
    string request_str;
    Request request;
    request.set_op(Request::GET);
    request.set_txnid(id);
    request.mutable_get()->set_key(key);
    request.SerializeToString(&request_str);

    // set to 1 second by default
    int timeout = (promise != NULL) ? promise->GetTimeout() : 1000;

    transport->Timer(0, [=]() {
	    waiting = promise;
        client->InvokeUnlogged(replica,
                               request_str,
                               bind(&ShardClient::GetCallback,
                                    this,
                                    placeholders::_1,
                                    placeholders::_2),
                               bind(&ShardClient::GetTimeout,
                                    this),
                               timeout); // timeout in ms
    });
}

void
ShardClient::Get(uint64_t id, const string &key,
                const Timestamp &timestamp, Promise *promise)
{
    // Send the GET operation to appropriate shard.
    Debug("[shard %i] Sending GET [%lu : %s]", shard, id, key.c_str());

    // create request
    string request_str;
    Request request;
    request.set_op(Request::GET);
    request.set_txnid(id);
    request.mutable_get()->set_key(key);
    timestamp.serialize(request.mutable_get()->mutable_timestamp());
    request.SerializeToString(&request_str);

    // set to 1 second by default
    int timeout = (promise != NULL) ? promise->GetTimeout() : 1000;

    transport->Timer(0, [=]() {
	    waiting = promise;
        client->InvokeUnlogged(
            replica,
            request_str,
            bind(&ShardClient::GetCallback, this,
                placeholders::_1,
                placeholders::_2),
            bind(&ShardClient::GetTimeout, this),
            timeout); // timeout in ms
    });
}

void
ShardClient::Put(uint64_t id,
               const string &key,
               const string &value,
               Promise *promise)
{
    Panic("Unimplemented PUT");
    return;
}

void
ShardClient::Prepare(uint64_t id, const Transaction &txn,
                    const Timestamp &timestamp, Promise *promise)
{
    Debug("[shard %i] Sending PREPARE [%lu]", shard, id);

    // create prepare request
    string request_str;
    Request request;
    request.set_op(Request::PREPARE);
    request.set_txnid(id);
    txn.serialize(request.mutable_prepare()->mutable_txn());
    timestamp.serialize(request.mutable_prepare()->mutable_timestamp());
    request.SerializeToString(&request_str);

    transport->Timer(0, [=]() {
        waiting = promise;
        client->InvokeConsensus(
            request_str,
            bind(&ShardClient::TapirDecide, this,
                placeholders::_1),
            bind(&ShardClient::PrepareCallback, this,
                placeholders::_1,
                placeholders::_2));
    });
}

std::string
ShardClient::TapirDecide(const std::map<std::string, std::size_t> &results)
{
    // If a majority say prepare_ok,
    int ok_count = 0;
    Timestamp ts = 0;
    string final_reply_str;
    Reply final_reply;

    for (const auto& string_and_count : results) {
        const std::string &s = string_and_count.first;
        const std::size_t count = string_and_count.second;

        Reply reply;
        reply.ParseFromString(s);

	if (reply.status() == REPLY_OK) {
	    ok_count += count;
	} else if (reply.status() == REPLY_FAIL) {
	    return s;
	} else if (reply.status() == REPLY_RETRY) {
	    Timestamp t(reply.timestamp());
	    if (t > ts) {
		ts = t;
	    }
	}
    }

    if (ok_count >= config->QuorumSize()) {
	final_reply.set_status(REPLY_OK);
    } else {
       final_reply.set_status(REPLY_RETRY);
       ts.serialize(final_reply.mutable_timestamp());
    }
    final_reply.SerializeToString(&final_reply_str);
    return final_reply_str;
}

void
ShardClient::Commit(uint64_t id, const Transaction &txn,
                   uint64_t timestamp, Promise *promise)
{

    Debug("[shard %i] Sending COMMIT [%lu]", shard, id);

    // create commit request
    string request_str;
    Request request;
    request.set_op(Request::COMMIT);
    request.set_txnid(id);
    request.mutable_commit()->set_timestamp(timestamp);
    request.SerializeToString(&request_str);

    blockingBegin = new Promise(COMMIT_TIMEOUT);
    transport->Timer(0, [=]() {
        waiting = promise;
        client->InvokeInconsistent(
            request_str,
            bind(&ShardClient::CommitCallback, this,
                placeholders::_1,
                placeholders::_2));
    });
}

void
ShardClient::Abort(uint64_t id, const Transaction &txn, Promise *promise)
{
    Debug("[shard %i] Sending ABORT [%lu]", shard, id);

    // create abort request
    string request_str;
    Request request;
    request.set_op(Request::ABORT);
    request.set_txnid(id);
    txn.serialize(request.mutable_abort()->mutable_txn());
    request.SerializeToString(&request_str);

    blockingBegin = new Promise(ABORT_TIMEOUT);
    transport->Timer(0, [=]() {
	    waiting = promise;
	    client->InvokeInconsistent(
            request_str,
            bind(&ShardClient::AbortCallback, this,
                placeholders::_1,
                placeholders::_2));
    });
}

void
ShardClient::GetTimeout()
{
    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        w->Reply(REPLY_TIMEOUT);
    }
}

/* Callback from a shard replica on get operation completion. */
void
ShardClient::GetCallback(const string &request_str, const string &reply_str)
{
    /* Replies back from a shard. */
    Reply reply;
    reply.ParseFromString(reply_str);

    Debug("[shard %lu:%i] GET callback [%d]", client_id, shard, reply.status());
    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        if (reply.has_timestamp()) {
            w->Reply(reply.status(), Timestamp(reply.timestamp()), reply.value());
        } else {
            w->Reply(reply.status(), reply.value());
        }
    }
}

/* Callback from a shard replica on prepare operation completion. */
void
ShardClient::PrepareCallback(const string &request_str, const string &reply_str)
{
    Reply reply;

    reply.ParseFromString(reply_str);
    Debug("[shard %lu:%i] PREPARE callback [%d]", client_id, shard, reply.status());

    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        if (reply.has_timestamp()) {
            w->Reply(reply.status(), Timestamp(reply.timestamp()));
        } else {
            w->Reply(reply.status(), Timestamp());
        }
    }
}

/* Callback from a shard replica on commit operation completion. */
void
ShardClient::CommitCallback(const string &request_str, const string &reply_str)
{
    // COMMITs always succeed.

    ASSERT(blockingBegin != NULL);
    blockingBegin->Reply(0);

    if (waiting != NULL) {
        waiting = NULL;
    }
    Debug("[shard %lu:%i] COMMIT callback", client_id, shard);
}

/* Callback from a shard replica on abort operation completion. */
void
ShardClient::AbortCallback(const string &request_str, const string &reply_str)
{
    // ABORTs always succeed.

    ASSERT(blockingBegin != NULL);
    blockingBegin->Reply(0);

    if (waiting != NULL) {
        waiting = NULL;
    }
    Debug("[shard %lu:%i] ABORT callback", client_id, shard);
}

} // namespace tapir
