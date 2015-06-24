// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * qwstore/client.h:
 *   QWstore client-side logic and APIs
 *
 **********************************************************************/

#ifndef _QW_CLIENT_H_
#define _QW_CLIENT_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "paxos-lib/lib/configuration.h"
#include "paxos-lib/lib/udptransport.h"
#include "paxos-lib/common/client.h"
#include "paxos-lib/vr/client.h"
#include "common/client.h"
#include "common/bufferclient.h"
#include "common/truetime.h"
#include "qwstore/qwclient.h"
#include "qwstore/qw-proto.pb.h"

#include <string>
#include <thread>
#include <set>

namespace qwstore {

class Client : public ::Client
{
public:
    Client(std::string configPath, int nshards, int closestReplica);
    ~Client();

    // Overriding methods from ::Client
    void Begin() {};
    int Get(const std::string &key, std::string &value);
    int Put(const std::string &key, const std::string &value);
    bool Commit() { return true; };
    void Abort() {};
    
private:
    /* Private helper functions. */
    void run_client(); // Runs the transport event loop.

    // Unique ID for this client.
    uint64_t client_id;

    // Number of shards in this deployment
    uint64_t nshards;

    // Transport used by shard clients.
    UDPTransport transport;
    
    // Thread running the transport event loop.
    std::thread *clientTransport;

    // Client for each shard.
    std::vector<QWClient *> bclient;
};

} // namespace qwstore

#endif /* _QW_CLIENT_H_ */
