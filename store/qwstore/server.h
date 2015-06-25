// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * qwstore/server.h:
 *   QWStore storage server executable and dispatch code
 *
 **********************************************************************/

#ifndef _QW_SERVER_H_
#define _QW_SERVER_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "lib/udptransport.h"
#include "lib/configuration.h"
#include "store/common/timestamp.h"
#include "store/common/transaction.h"
#include "qwstore.h"
#include "store/qwstore/qw-proto.pb.h"

namespace qwstore {

class Server : TransportReceiver
{
private:
    // Underlying single node transactional key-value store.
    QWStore *store;

    // Configuration of replicas.
    specpaxos::Configuration configuration;

    // Index of 'this' replica, and handle to transport layer.
    int myIdx;
    Transport *transport;

public:
    Server(const specpaxos::Configuration &configuration, int myIdx,
           Transport *transport, QWStore *store);
    ~Server();

    void ReceiveMessage(const TransportAddress &remote,
                        const std::string &type, const std::string &data);

    void HandleMessage(const TransportAddress &remote,
                        const std::string &type, const std::string &data);
    void HandleGet(const TransportAddress &remote,
                   const proto::GetMessage &msg);
    void HandlePut(const TransportAddress &remote,
                   const proto::PutMessage &msg);

    void Load(const std::string &key, const std::string &value);

};


} // namespace qwstore

#endif /* _QW_SERVER_H_ */
