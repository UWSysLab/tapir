// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/tapir/shardclient.cc:
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

#include "store/tapir/shardclient.h"

namespace tapir {

using namespace std;
using namespace proto;

TapirClient::TapirClient(const string &configPath,
                       Transport *transport, uint64_t client_id, int
                       shard, int closestReplica)
    : transport(transport), client_id(client_id), shard(shard)
{ 
    ifstream configStream(configPath);
    if (configStream.fail()) {
        fprintf(stderr, "unable to read configuration file: %s\n",
                configPath.c_str());
    }
    transport::Configuration config(configStream);

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

TapirClient::~TapirClient()
{ 
    delete client;
}

void
TapirClient::Begin(uint64_t id)
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
TapirClient::Get(uint64_t id, const string &key, Promise *promise)
{
    // Send the GET operation to appropriate shard.
    Debug("[shard %i] Sending GET [%s]", shard, key.c_str());

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
                               bind(&TapirClient::GetCallback,
                                    this,
                                    placeholders::_1,
                                    placeholders::_2),
                               bind(&TapirClient::GetTimeout,
                                    this),
                               timeout); // timeout in ms
    });
}

void
TapirClient::Get(uint64_t id, const string &key,
                const Timestamp &timestamp, Promise *promise)
{
    // Send the GET operation to appropriate shard.
    Debug("[shard %i] Sending GET [%s]", shard, key.c_str());

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
            bind(&TapirClient::GetCallback, this,
                placeholders::_1,
                placeholders::_2),
            bind(&TapirClient::GetTimeout, this),
            timeout); // timeout in ms
    });
}

void
TapirClient::Prepare(uint64_t id, const Transaction &txn,
                    const Timestamp &timestamp, Promise *promise)
{
    Debug("[shard %i] Sending PREPARE: %lu", shard, id);

    // create prepare request
    string request_str;
    Request request;
    request.set_op(Request::PREPARE);
    request.set_txnid(id);
    txn.serialize(request.mutable_prepare()->mutable_txn());
    request.SerializeToString(&request_str);

    transport->Timer(0, [=]() {
        waiting = promise;
        client->InvokeConsensus(
            request_str,
            bind(&TapirClient::TapirDecide, this,
                placeholders::_1),
            bind(&TapirClient::PrepareCallback, this,
                placeholders::_1,
                placeholders::_2));
    });
}

void
TapirClient::Commit(uint64_t id, const Transaction &txn,
                   uint64_t timestamp, Promise *promise)
{

    Debug("[shard %i] Sending COMMIT: %lu", shard, id);

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
            bind(&TapirClient::CommitCallback, this,
                placeholders::_1,
                placeholders::_2));
    });
}

void
TapirClient::Abort(uint64_t id, const Transaction &txn, Promise *promise)
{
    Debug("[shard %i] Sending ABORT: %lu", shard, id);
    
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
            bind(&TapirClient::AbortCallback, this,
                placeholders::_1,
                placeholders::_2));
    });
}

void
TapirClient::GetTimeout()
{
    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        w->Reply(REPLY_TIMEOUT);
    }
}

/* Callback from a shard replica on get operation completion. */
void
TapirClient::GetCallback(const string &request_str, const string &reply_str)
{
    /* Replies back from a shard. */
    Reply reply;
    reply.ParseFromString(reply_str);

    Debug("[shard %i] Received GET callback [%d]", shard, reply.status());
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
TapirClient::PrepareCallback(const string &request_str, const string &reply_str)
{
    Reply reply;

    reply.ParseFromString(reply_str);
    Debug("[shard %i] Received PREPARE callback [%d]", shard, reply.status());

    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        if (reply.has_timestamp()) {
            w->Reply(reply.status(), Timestamp(reply.timestamp(), 0));
        } else {
            w->Reply(reply.status(), Timestamp());
        }
    }
}

/* Callback from a shard replica on commit operation completion. */
void
TapirClient::CommitCallback(const string &request_str, const string &reply_str)
{
    // COMMITs always succeed.
    Reply reply;
    reply.ParseFromString(reply_str);
    ASSERT(reply.status() == REPLY_OK);

    ASSERT(blockingBegin != NULL);
    blockingBegin->Reply(0);

    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        w->Reply(reply.status());
    }
    Debug("[shard %i] Received COMMIT callback [%d]", shard, reply.status());
}

/* Callback from a shard replica on abort operation completion. */
void
TapirClient::AbortCallback(const string &request_str, const string &reply_str)
{
    // ABORTs always succeed.
    Reply reply;
    reply.ParseFromString(reply_str);
    ASSERT(reply.status() == REPLY_OK);

    ASSERT(blockingBegin != NULL);
    blockingBegin->Reply(0);

    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        w->Reply(reply.status());
    }
    Debug("[shard %i] Received ABORT callback [%d]", shard, reply.status());
}

} // namespace tapir
