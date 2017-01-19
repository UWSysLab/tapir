// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/weakstore/shardclient.cc
 *   Client for one weak consistency store shard.
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

#include "store/weakstore/shardclient.h"

namespace weakstore {

using namespace std;
using namespace proto;

ShardClient::ShardClient(string configPath, Transport *transport,
                   uint64_t client_id, int shard, int closestReplica) :
    transport(transport), client_id(client_id), shard(shard)
{ 
    ifstream configStream(configPath);
    if (configStream.fail()) {
        fprintf(stderr, "unable to read configuration file: %s\n",
                configPath.c_str());
    }
    config = new transport::Configuration(configStream);
    transport->Register(this, *config, -1);
    
    timeout = new Timeout(transport, 250, [this]() {
            RequestTimedOut();
        });
    
    if (closestReplica == -1) {
        replica = client_id % config->n;
    } else {
        replica = closestReplica;
    }
    
    waiting = NULL;
}

ShardClient::~ShardClient() 
{ 
    delete config;
    delete timeout;
}

void
ShardClient::Get(uint64_t id, const string &key, Promise *promise)
{
    // Create get request
    GetMessage msg;
    msg.set_clientid(client_id);
    msg.set_key(key);

    ASSERT(waiting == NULL);

    waiting = promise;

    // Send message
    transport->Timer(0, [=]() {
            if (transport->SendMessageToReplica(this, replica, msg)) {                
                if (waiting != NULL) {
                    timeout->SetTimeout(promise->GetTimeout());
                    timeout->Start();
                }
            } else if (waiting != NULL) {
                Promise *w = waiting;
                waiting = NULL;
                w->Reply(REPLY_NETWORK_FAILURE);
            }
        });
}

void
ShardClient::Put(uint64_t id,
              const string &key,
              const string &value,
              Promise *promise)
{
    Debug("[shard %d] Sending PUT [%s %s]", shard, key.c_str(), value.c_str());

    // Creating put request
    PutMessage msg;
    msg.set_clientid(client_id);
    msg.set_key(key);
    msg.set_value(value);

    ASSERT(waiting == NULL);

    waiting = promise;
    // clear the reply counter
    totalReplies = 0;

    // Send messages
    transport->Timer(0, [=]() {
            // always send to leader for now
            if (transport->SendMessageToAll(this, msg)) {
                // set the timeout
                if (waiting != NULL) {
                    timeout->SetTimeout(waiting->GetTimeout());
                    timeout->Start();
                }
            } else if (waiting != NULL) {
                Promise *w = waiting;
                waiting = NULL;
                w->Reply(REPLY_NETWORK_FAILURE);
            }
        });

}

// Callbacks that happen in the transport thread
void
ShardClient::RequestTimedOut()
{
    Debug("[shard %d] Timeout", shard);
    
    timeout->Stop();

    if (waiting != NULL) {
        Promise *w = waiting;
        waiting = NULL;
        w->Reply(REPLY_TIMEOUT);
    }
}

void
ShardClient::ReceiveMessage(const TransportAddress &remote,
                         const string &type,
                         const string &data)
{
    GetReplyMessage getReply;
    PutReplyMessage putReply;
  
    Debug("Received reply type: %s", type.c_str());

    if (type == getReply.GetTypeName()) {
        getReply.ParseFromString(data);
        if (waiting != NULL) {
            timeout->Stop();
            Promise *w = waiting;
            waiting = NULL;
            w->Reply(getReply.status(),getReply.value());
        }
    } else if (type == putReply.GetTypeName()) {
        totalReplies++;
        if (totalReplies >= config->n) {
            if (waiting != NULL) {
                timeout->Stop();
                Promise *w = waiting;
                waiting = NULL;
                w->Reply(REPLY_OK);
            }
        }
    } else {
        NOT_REACHABLE();
    }
}

} // namespace weakstore
