// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * spanstore/client.h:
 *   SpanStore client interface.
 *
 **********************************************************************/

#ifndef _SPAN_CLIENT_H_
#define _SPAN_CLIENT_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "paxos-lib/lib/configuration.h"
#include "paxos-lib/lib/udptransport.h"
#include "paxos-lib/common/client.h"
#include "paxos-lib/vr/client.h"
#include "common/client.h"
#include "common/bufferclient.h"
#include "common/truetime.h"
#include "common/txnstore.h"
#include "spanstore/spanclient.h"
#include "spanstore/span-proto.pb.h"

#include <condition_variable>
#include <mutex>
#include <string>
#include <set>
#include <thread>

namespace spanstore {

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
    specpaxos::Client *tss; 

    // TrueTime server.
    TrueTime timeServer;

    // Synchronization variables.
    std::condition_variable cv;
    std::mutex cv_m;
    string replica_reply;

    // Time spend sleeping for commit.
    int commit_sleep;
};

} // namespace spanstore

#endif /* _SPAN_CLIENT_H_ */
