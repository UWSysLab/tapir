// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/tapirstore/client.cc:
 *   Client to TAPIR transactional storage system.
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

#include "store/tapirstore/client.h"

namespace tapirstore {

using namespace std;

Client::Client(const string configPath, int nShards,
                int closestReplica, TrueTime timeServer)
    : nshards(nShards), transport(0.0, 0.0, 0, false), timeServer(timeServer)
{
    // Initialize all state here;
    client_id = 0;
    while (client_id == 0) {
        random_device rd;
        mt19937_64 gen(rd());
        uniform_int_distribution<uint64_t> dis;
        client_id = dis(gen);
    }
    t_id = (client_id/10000)*10000;

    bclient.reserve(nshards);

    Debug("Initializing Tapir client with id [%lu] %lu", client_id, nshards);

    /* Start a client for each shard. */
    for (uint64_t i = 0; i < nshards; i++) {
        string shardConfigPath = configPath + to_string(i) + ".config";
        ShardClient *shardclient = new ShardClient(shardConfigPath,
                &transport, client_id, i, closestReplica);
        bclient[i] = new BufferClient(shardclient);
    }

    Debug("Tapir client [%lu] created! %lu %lu", client_id, nshards, bclient.size());

    /* Run the transport in a new thread. */
    clientTransport = new thread(&Client::run_client, this);

    Debug("Tapir client [%lu] created! %lu", client_id, bclient.size());
}

Client::~Client()
{
    transport.Stop();
    for (auto b : bclient) {
        delete b;
    }
    clientTransport->join();
}

/* Runs the transport event loop. */
void
Client::run_client()
{
    transport.Run();
}

/* Begins a transaction. All subsequent operations before a commit() or
 * abort() are part of this transaction.
 *
 * Return a TID for the transaction.
 */
void
Client::Begin()
{
    Debug("BEGIN [%lu]", t_id + 1);
    t_id++;
    participants.clear();
}

/* Returns the value corresponding to the supplied key. */
int
Client::Get(const string &key, string &value)
{
    Debug("GET [%lu : %s]", t_id, key.c_str());

    // Contact the appropriate shard to get the value.
    int i = key_to_shard(key, nshards);

    // If needed, add this shard to set of participants and send BEGIN.
    if (participants.find(i) == participants.end()) {
        participants.insert(i);
        bclient[i]->Begin(t_id);
    }

    // Send the GET operation to appropriate shard.
    Promise promise(GET_TIMEOUT);

    bclient[i]->Get(key, &promise);
    value = promise.GetValue();
    return promise.GetReply();
}

string
Client::Get(const string &key)
{
    string value;
    Get(key, value);
    return value;
}

/* Sets the value corresponding to the supplied key. */
int
Client::Put(const string &key, const string &value)
{
    Debug("PUT [%lu : %s]", t_id, key.c_str());

    // Contact the appropriate shard to set the value.
    int i = key_to_shard(key, nshards);

    // If needed, add this shard to set of participants and send BEGIN.
    if (participants.find(i) == participants.end()) {
        participants.insert(i);
        bclient[i]->Begin(t_id);
    }

    Promise promise(PUT_TIMEOUT);

    // Buffering, so no need to wait.
    bclient[i]->Put(key, value, &promise);
    return promise.GetReply();
}

int
Client::Prepare(Timestamp &timestamp)
{
    // 1. Send commit-prepare to all shards.
    uint64_t proposed = 0;
    list<Promise *> promises;

    Debug("PREPARE [%lu] at %lu", t_id, timestamp.getTimestamp());
    ASSERT(participants.size() > 0);

    for (auto p : participants) {
        promises.push_back(new Promise(PREPARE_TIMEOUT));
        bclient[p]->Prepare(timestamp, promises.back());
    }

    int status = REPLY_OK;
    uint64_t ts;
    // 3. If all votes YES, send commit to all shards.
    // If any abort, then abort. Collect any retry timestamps.
    for (auto p : promises) {
        uint64_t proposed = p->GetTimestamp().getTimestamp();

        switch(p->GetReply()) {
        case REPLY_OK:
            Debug("PREPARE [%lu] OK", t_id);
            continue;
        case REPLY_FAIL:
            // abort!
            Debug("PREPARE [%lu] ABORT", t_id);
            return REPLY_FAIL;
        case REPLY_RETRY:
            status = REPLY_RETRY;
                if (proposed > ts) {
                    ts = proposed;
                }
                break;
        case REPLY_TIMEOUT:
            status = REPLY_RETRY;
            break;
        case REPLY_ABSTAIN:
            // just ignore abstains
            break;
        default:
            break;
        }
        delete p;
    }

    if (status == REPLY_RETRY) {
        uint64_t now = timeServer.GetTime();
        if (now > proposed) {
            timestamp.setTimestamp(now);
        } else {
            timestamp.setTimestamp(proposed);
        }
        Debug("RETRY [%lu] at [%lu]", t_id, timestamp.getTimestamp());
    }

    Debug("All PREPARE's [%lu] received", t_id);
    return status;
}

/* Attempts to commit the ongoing transaction. */
bool
Client::Commit()
{
    // Implementing 2 Phase Commit
    Timestamp timestamp(timeServer.GetTime(), client_id);
    int status;

    for (retries = 0; retries < COMMIT_RETRIES; retries++) {
        status = Prepare(timestamp);
        if (status == REPLY_RETRY) {
            continue;
        } else {
            break;
        }
    }

    if (status == REPLY_OK) {
        Debug("COMMIT [%lu]", t_id);
        
        for (auto p : participants) {
            bclient[p]->Commit(0);
        }
        return true;
    }

    // 4. If not, send abort to all shards.
    Abort();
    return false;
}

/* Aborts the ongoing transaction. */
void
Client::Abort()
{
    Debug("ABORT [%lu]", t_id);

    for (auto p : participants) {
        bclient[p]->Abort();
    }
}

/* Return statistics of most recent transaction. */
vector<int>
Client::Stats()
{
    vector<int> v;
    return v;
}

} // namespace tapirstore
