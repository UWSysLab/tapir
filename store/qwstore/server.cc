// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * qwstore/server.cc:
 *   QWStore storage server. Mostly dispatch code
 *
 **********************************************************************/

#include "qwstore/server.h"

namespace qwstore {

using namespace proto;

Server::Server(const specpaxos::Configuration &configuration, int myIdx,
               Transport *transport, QWStore *store)
    : store(store), configuration(configuration), myIdx(myIdx), transport(transport)
{
    transport->Register(this, configuration, myIdx);
}

Server::~Server() { }

void
Server::ReceiveMessage(const TransportAddress &remote,
                       const string &type, const string &data)
{
#if CLIENT_NETWORK_DELAY
    TransportAddress *r = remote.clone();
    transport->Timer(CLIENT_NETWORK_DELAY, [=]() {
            HandleMessage(*r, type, data);
            delete r;
        });
#else
    HandleMessage(remote, type, data);
#endif

}

void
Server::HandleMessage(const TransportAddress &remote,
                      const string &type, const string &data)
{
    static GetMessage get;
    static PutMessage put;
    
    if (type == get.GetTypeName()) {
        get.ParseFromString(data);
        HandleGet(remote, get);
    } else if (type == put.GetTypeName()) {
        put.ParseFromString(data);
        HandlePut(remote, put);
    } else {
        Panic("Received unexpected message type in OR proto: %s",
              type.c_str());
    }
}

void
Server::HandleGet(const TransportAddress &remote,
                  const GetMessage &msg)
{
    int status;
    string value;
    
    status = store->Get(msg.clientid(), msg.key(), value);

    GetReplyMessage reply;
    reply.set_status(status);
    reply.set_value(value);
    
    transport->SendMessage(this, remote, reply);
}

void
Server::HandlePut(const TransportAddress &remote,
                  const PutMessage &msg)
{
    int status = store->Put(msg.clientid(), msg.key(), msg.value());
    PutReplyMessage reply;
    reply.set_status(status);
    
    transport->SendMessage(this, remote, reply);
}

void
Server::Load(const string &key, const string &value)
{
    store->Load(key, value);
}

} // namespace qwstore
