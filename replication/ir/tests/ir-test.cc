// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * ir-test.cc:
 *   test cases for Inconsistent Replication Protocol
 *
 * Copyright 2013 Dan R. K. Ports  <drkp@cs.washington.edu>
 * Copyright 2015 Irene Zhang Ports  <iyzhang@cs.washington.edu>
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

#include "lib/configuration.h"
#include "lib/message.h"
#include "lib/transport.h"
#include "lib/simtransport.h"

#include "replication/common/client.h"
#include "replication/common/replica.h"
#include "replication/ir/client.h"
#include "replication/ir/replica.h"

#include <stdlib.h>
#include <stdio.h>
#include <gtest/gtest.h>
#include <vector>
#include <set>
#include <sstream>

static string replicaLastOp;
static string clientLastOp;
static string clientLastReply;

using google::protobuf::Message;
using namespace replication;
using namespace replication::ir;
using namespace replication::ir::proto;

class IRApp : public IRAppReplica {

    std::vector<string> *iOps;
    std::vector<string> *cOps;
    std::vector<string> *unloggedOps;

public:
    IRApp(std::vector<string> *i, std::vector<string> *c, std::vector<string> *u) : iOps(i), cOps(c), unloggedOps(u) { }
    
    void ExecInconsistentUpcall(const string &req) {
        iOps->push_back(req);
    }

    void ExecConsensusUpcall(const string &req, string &reply) {
        cOps->push_back(req);
        reply = "reply: " + req;
    }
    
    void UnloggedUpcall(const string &req, string &reply) {
        unloggedOps->push_back(req);
        reply = "unlreply: " + req;
    }
};
    
class IRTest : public  ::testing::Test
{
protected:
    std::vector<IRReplica *> replicas;
    IRClient *client;
    SimulatedTransport *transport;
    transport::Configuration *config;
    std::vector<std::vector<string> > iOps;
    std::vector<std::vector<string> > cOps;
    std::vector<std::vector<string> > unloggedOps;
    int requestNum;
    
    virtual void SetUp() {
        std::vector<transport::ReplicaAddress> replicaAddrs =
            { { "localhost", "12345" },
              { "localhost", "12346" },
              { "localhost", "12347" }};
        config = new transport::Configuration(3, 1, replicaAddrs);

        transport = new SimulatedTransport();
        
        iOps.resize(config->n);
        cOps.resize(config->n);
        unloggedOps.resize(config->n);

        for (int i = 0; i < config->n; i++) {
            replicas.push_back(new IRReplica(*config, i, transport,
                                             new IRApp(&iOps[i], &cOps[i], &unloggedOps[i])));
        }

        client = new IRClient(*config, transport);
        requestNum = -1;

        // Only let tests run for a simulated minute. This prevents
        // infinite retry loops, etc.
//        transport->Timer(60000, [&]() {
//                transport->CancelAllTimers();
//            });
    }

    virtual string RequestOp(int n) {
        std::ostringstream stream;
        stream << "test: " << n;
        return stream.str();
    }

    virtual string LastRequestOp() {
        return RequestOp(requestNum);
    }
    
    virtual void ClientSendNextInconsistent(Client::continuation_t upcall) {
        requestNum++;
        client->InvokeInconsistent(LastRequestOp(), upcall);
    }

    virtual void ClientSendNextConsensus(Client::continuation_t upcall, IRClient::decide_t decide) {
        requestNum++;
        client->InvokeConsensus(LastRequestOp(), decide, upcall);
    }

    virtual void ClientSendNextUnlogged(int idx, Client::continuation_t upcall,
                                        Client::timeout_continuation_t timeoutContinuation = nullptr,
                                        uint32_t timeout = Client::DEFAULT_UNLOGGED_OP_TIMEOUT) {
        requestNum++;
        client->InvokeUnlogged(idx, LastRequestOp(), upcall, timeoutContinuation, timeout);
    }
    
    virtual void TearDown() {
        for (auto x : replicas) {
            delete x;
        }
        
        replicas.clear();
        iOps.clear();
        cOps.clear();
        unloggedOps.clear();

        delete client;
        delete transport;
        delete config;
    }
};

TEST_F(IRTest, OneInconsistentOp)
{
    auto upcall = [this](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());

        // Inconsistent ops do not return a value
        EXPECT_EQ(reply, "");
        
        transport->CancelAllTimers();
    };
    
    ClientSendNextInconsistent(upcall);
    transport->Run();

    // By now, they all should have executed the last request.
    for (int i = 0; i < config->n; i++) {
        EXPECT_EQ(iOps[i].size(), 1);
        EXPECT_EQ(iOps[i].back(),  LastRequestOp());
    }
}

TEST_F(IRTest, OneConsensusOp)
{
    auto upcall = [this](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());

        transport->CancelAllTimers();
    };

    auto decide = [this](const std::set<string> &results) {
        // shouldn't ever get called
        EXPECT_FALSE(true);

        return "";
    };

    ClientSendNextConsensus(upcall, decide);
    transport->Run();

    // By now, they all should have executed the last request.
    for (int i = 0; i < config->n; i++) {
        EXPECT_EQ(cOps[i].size(), 1);
        EXPECT_EQ(cOps[i].back(),  LastRequestOp());
    }
}

TEST_F(IRTest, Unlogged)
{
    auto upcall = [this](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "unlreply: "+LastRequestOp());

        EXPECT_EQ(unloggedOps[1].back(), req);
        transport->CancelAllTimers();
    };
    int timeouts = 0;
    auto timeout = [&](const string &req) {
        timeouts++;
    };
    
    ClientSendNextUnlogged(1, upcall, timeout);
    transport->Run();

    for (unsigned int i = 0; i < iOps.size(); i++) {
        EXPECT_EQ(0, iOps[i].size());
        EXPECT_EQ((i == 1 ? 1 : 0), unloggedOps[i].size());
    }
    EXPECT_EQ(0, timeouts);
}

TEST_F(IRTest, UnloggedTimeout)
{
    auto upcall = [this](const string &req, const string &reply) {
        FAIL();
        transport->CancelAllTimers();
    };
    int timeouts = 0;
    auto timeout = [&](const string &req) {
        timeouts++;
    };

    // Drop messages to or from replica 1
    transport->AddFilter(10, [](TransportReceiver *src, int srcIdx,
                                TransportReceiver *dst, int dstIdx,
                                Message &m, uint64_t &delay) {
                             if ((srcIdx == 1) || (dstIdx == 1)) {
                                 return false;
                             }
                             return true;
                         });

    // Run for 10 seconds
    transport->Timer(10000, [&]() {
            transport->CancelAllTimers();
        });

    ClientSendNextUnlogged(1, upcall, timeout);
    transport->Run();

    for (unsigned int i = 0; i < iOps.size(); i++) {
        EXPECT_EQ(0, iOps[i].size());
        EXPECT_EQ(0, unloggedOps[i].size());
    }
    EXPECT_EQ(1, timeouts);
}


// TEST_F(IRTest, ManyOps)
// {
//     Client::continuation_t upcall = [&](const string &req, const string &reply) {
//         EXPECT_EQ(req, LastRequestOp());
//         EXPECT_EQ(reply, "reply: "+LastRequestOp());

//         // Not guaranteed that any replicas except the leader have
//         // executed this request.
//         EXPECT_EQ(ops[0].back(), req);

//         if (requestNum < 9) {
//             ClientSendNext(upcall);
//         } else {
//             transport->CancelAllTimers();
//         }
//     };
    
//     ClientSendNext(upcall);
//     transport->Run();

//     // By now, they all should have executed the last request.
//     for (int i = 0; i < config->n; i++) {
//         EXPECT_EQ(10, ops[i].size());
//         for (int j = 0; j < 10; j++) {
//             EXPECT_EQ(RequestOp(j), ops[i][j]);            
//         }
//     }
// }

