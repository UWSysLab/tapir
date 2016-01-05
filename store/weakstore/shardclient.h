// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * weakstore/weakclient.h
 *   Client-side module for talking to a single shard weak consistency storage server
 *
 **********************************************************************/

#ifndef _WEAK_SHARDCLIENT_H_
#define _WEAK_SHARDCLIENT_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "paxos-lib/lib/configuration.h"
#include "paxos-lib/lib/udptransport.h"
#include "common/timestamp.h"
#include "common/transaction.h"
#include "common/txnclient.h"
#include "weakstore/weak-proto.pb.h"

#include <set>
#include <thread>

#define COMMIT_RETRIES 5

namespace weakstore {

class ShardClient : public TransportReceiver
{
public:
    ShardClient(std::string configPath,
             Transport *transport,
             uint64_t client_id,
             int shard,
             int closestReplica);
    ~ShardClient();

    void Get(uint64_t id, const std::string &key, Promise *promise);
    void Put(uint64_t id, const std::string &key, const std::string &value, Promise *promise);
    
    // Overriding from TransportReceiver
    void ReceiveMessage(const TransportAddress &remote, const std::string &type, const std::string &data);

private:
    transport::Configuration *config;
    Transport *transport;  // Transport to replicas

    uint64_t client_id;
    int shard;
    int replica;

    Timeout *timeout; // Timeout for general requests

    int totalReplies;
    Promise *waiting;

    void RequestTimedOut();
};

} // namespace weakstore

#endif /* _WEAK_SHARDCLIENT_H_ */
