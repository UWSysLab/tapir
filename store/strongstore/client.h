// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/strongstore/client.h:
 *   Transactional client interface.
 *
 * Copyright 2015 Irene Zhang  <iyzhang@cs.washington.edu>
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
 
#ifndef _STRONG_CLIENT_H_
#define _STRONG_CLIENT_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "lib/configuration.h"
#include "lib/udptransport.h"
#include "replication/vr/client.h"
#include "store/common/frontend/bufferclient.h"
#include "store/common/frontend/client.h"
#include "store/common/truetime.h"
#include "store/strongstore/strong-proto.pb.h"
#include "store/strongstore/shardclient.h"

#include <set>
#include <thread>

namespace strongstore {

class Client : public ::Client
{
public:
    Client(Mode mode, string configPath, int nshards,
            int closestReplica, TrueTime timeServer);
    ~Client();

    // Overriding functions from ::Client
    void Begin();
    int Get(const string &key, string &value);
    int Put(const string &key, const string &value);
    bool Commit();
    void Abort();
    std::vector<int> Stats();

private:
    /* Private helper functions. */
    void run_client(); // Runs the transport event loop.

    // timestamp server call back
    void tssCallback(const string &request, const string &reply);

    // local Prepare function
    int Prepare(uint64_t &ts);

    // Unique ID for this client.
    uint64_t client_id;

    // Ongoing transaction ID.
    uint64_t t_id;

    // Number of shards in SpanStore.
    long nshards;

    // List of participants in the ongoing transaction.
    std::set<int> participants;

    // Transport used by paxos client proxies.
    UDPTransport transport;
    
    // Thread running the transport event loop.
    std::thread *clientTransport;

    // Buffering client for each shard.
    std::vector<BufferClient *> bclient;

    // Mode in which spanstore runs.
    Mode mode;

    // Timestamp server shard.
    replication::vr::VRClient *tss; 

    // TrueTime server.
    TrueTime timeServer;

    // Synchronization variables.
    std::condition_variable cv;
    std::mutex cv_m;
    string replica_reply;

    // Time spend sleeping for commit.
    int commit_sleep;
};

} // namespace strongstore

#endif /* _STRONG_CLIENT_H_ */
