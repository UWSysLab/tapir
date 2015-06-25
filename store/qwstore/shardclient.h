// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * qwstore/qwclient.h
 *   Client-side module for QWStore clients.
 *
 **********************************************************************/

#ifndef _QW_TXN_CLIENT_H_
#define _QW_TXN_CLIENT_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "paxos-lib/lib/configuration.h"
#include "paxos-lib/lib/udptransport.h"
#include "common/timestamp.h"
#include "common/transaction.h"
#include "common/txnclient.h"
#include "qwstore/qw-proto.pb.h"

#include <set>
#include <thread>

#define COMMIT_RETRIES 5

namespace qwstore {

class QWClient : public TransportReceiver
{
public:
    QWClient(std::string configPath,
             Transport *transport,
             uint64_t client_id,
             int shard,
             int closestReplica);
    ~QWClient();

    void Get(uint64_t id, const std::string &key, Promise *promise);
    void Put(uint64_t id, const std::string &key, const std::string &value, Promise *promise);
    
    // Overriding from TransportReceiver
    void ReceiveMessage(const TransportAddress &remote, const std::string &type, const std::string &data);

private:
    specpaxos::Configuration *config;
    Transport *transport;  // Transport to replicas

    uint64_t client_id;
    int shard;
    int replica;

    Timeout *timeout; // Timeout for general requests

    int totalReplies;
    Promise *waiting;

    void RequestTimedOut();
};

} // namespace qwstore

#endif /* _QW_TXN_CLIENT_H_ */
