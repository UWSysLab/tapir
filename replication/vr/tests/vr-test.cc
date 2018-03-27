// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * vr-test.cc:
 *   test cases for Viewstamped Replication protocol
 *
 * Copyright 2013 Dan R. K. Ports  <drkp@cs.washington.edu>
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
#include "replication/vr/client.h"
#include "replication/vr/replica.h"

#include <stdlib.h>
#include <stdio.h>
#include <gtest/gtest.h>
#include <vector>
#include <sstream>

static string replicaLastOp;
static string clientLastOp;
static string clientLastReply;

using google::protobuf::Message;
using namespace replication;
using namespace replication::vr;
using namespace replication::vr::proto;

class VRApp : public AppReplica {

    std::vector<string> *ops;
    std::vector<string> *unloggedOps;

public:
    VRApp(std::vector<string> *o, std::vector<string> *u) : ops(o), unloggedOps(u) { }

    void ReplicaUpcall(opnum_t opnum, const string &req, string &reply) {
        ops->push_back(req);
        reply = "reply: " + req;
    }

    void UnloggedUpcall(const string &req, string &reply) {
        unloggedOps->push_back(req);
        reply = "unlreply: " + req;
    }
};

class VRTest : public  ::testing::TestWithParam<int>
{
protected:
    std::vector<VRReplica *> replicas;
    VRClient *client;
    SimulatedTransport *transport;
    transport::Configuration *config;
    std::vector<std::vector<string> > ops;
    std::vector<std::vector<string> > unloggedOps;
    int requestNum;

    virtual void SetUp() {
        std::vector<transport::ReplicaAddress> replicaAddrs =
            { { "localhost", "12345" },
              { "localhost", "12346" },
              { "localhost", "12347" }};
        config = new transport::Configuration(3, 1, replicaAddrs);

        transport = new SimulatedTransport();

        ops.resize(config->n);
        unloggedOps.resize(config->n);

        for (int i = 0; i < config->n; i++) {
            replicas.push_back(new VRReplica(*config, i, transport, GetParam(), new VRApp(&ops[i], &unloggedOps[i])));
        }

        client = new VRClient(*config, transport);
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

    virtual void ClientSendNext(Client::continuation_t upcall) {
        requestNum++;
        client->Invoke(LastRequestOp(), upcall);
    }

    virtual void ClientSendNextUnlogged(int idx, Client::continuation_t upcall,
                                        Client::error_continuation_t error_continuation = nullptr,
                                        uint32_t timeout = Client::DEFAULT_UNLOGGED_OP_TIMEOUT) {
        requestNum++;
        client->InvokeUnlogged(idx, LastRequestOp(), upcall, error_continuation, timeout);
    }

    virtual void TearDown() {
        for (auto x : replicas) {
            delete x;
        }

        replicas.clear();
        ops.clear();
        unloggedOps.clear();

        delete client;
        delete transport;
        delete config;
    }
};

TEST_P(VRTest, OneOp)
{
    auto upcall = [this](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());

        // Not guaranteed that any replicas except the leader have
        // executed this request.
        EXPECT_EQ(ops[0].back(), req);
        transport->CancelAllTimers();
    };

    ClientSendNext(upcall);
    transport->Run();

    // By now, they all should have executed the last request.
    for (int i = 0; i < config->n; i++) {
        EXPECT_EQ(ops[i].size(), 1);
        EXPECT_EQ(ops[i].back(),  LastRequestOp());
    }
}

TEST_P(VRTest, Unlogged)
{
    auto upcall = [this](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "unlreply: "+LastRequestOp());

        EXPECT_EQ(unloggedOps[1].back(), req);
        transport->CancelAllTimers();
    };
    int timeouts = 0;
    auto timeout = [&](const string &req, ErrorCode) {
        timeouts++;
    };

    ClientSendNextUnlogged(1, upcall, timeout);
    transport->Run();

    for (unsigned int i = 0; i < ops.size(); i++) {
        EXPECT_EQ(0, ops[i].size());
        EXPECT_EQ((i == 1 ? 1 : 0), unloggedOps[i].size());
    }
    EXPECT_EQ(0, timeouts);
}

TEST_P(VRTest, UnloggedTimeout)
{
    auto upcall = [this](const string &req, const string &reply) {
        FAIL();
        transport->CancelAllTimers();
    };
    int timeouts = 0;
    auto timeout = [&](const string &req, ErrorCode) {
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

    for (unsigned int i = 0; i < ops.size(); i++) {
        EXPECT_EQ(0, ops[i].size());
        EXPECT_EQ(0, unloggedOps[i].size());
    }
    EXPECT_EQ(1, timeouts);
}


TEST_P(VRTest, ManyOps)
{
    Client::continuation_t upcall = [&](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());

        // Not guaranteed that any replicas except the leader have
        // executed this request.
        EXPECT_EQ(ops[0].back(), req);

        if (requestNum < 9) {
            ClientSendNext(upcall);
        } else {
            transport->CancelAllTimers();
        }
    };

    ClientSendNext(upcall);
    transport->Run();

    // By now, they all should have executed the last request.
    for (int i = 0; i < config->n; i++) {
        EXPECT_EQ(10, ops[i].size());
        for (int j = 0; j < 10; j++) {
            EXPECT_EQ(RequestOp(j), ops[i][j]);
        }
    }
}

TEST_P(VRTest, FailedReplica)
{
    Client::continuation_t upcall = [&](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());

        // Not guaranteed that any replicas except the leader have
        // executed this request.
        EXPECT_EQ(ops[0].back(), req);

        if (requestNum < 9) {
            ClientSendNext(upcall);
        } else {
            transport->CancelAllTimers();
        }
    };

    ClientSendNext(upcall);

    // Drop messages to or from replica 1
    transport->AddFilter(10, [](TransportReceiver *src, int srcIdx,
                                TransportReceiver *dst, int dstIdx,
                                Message &m, uint64_t &delay) {
                             if ((srcIdx == 1) || (dstIdx == 1)) {
                                 return false;
                             }
                             return true;
                         });

    transport->Run();

    // By now, they all should have executed the last request.
    for (int i = 0; i < config->n; i++) {
        if (i == 1) {
            continue;
        }
        EXPECT_EQ(10, ops[i].size());
        for (int j = 0; j < 10; j++) {
            EXPECT_EQ(RequestOp(j), ops[i][j]);
        }
    }
}

TEST_P(VRTest, StateTransfer)
{
    Client::continuation_t upcall = [&](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());

        // Not guaranteed that any replicas except the leader have
        // executed this request.
        EXPECT_EQ(ops[0].back(), req);

        if (requestNum == 5) {
            // Restore replica 1
            transport->RemoveFilter(10);
        }

        if (requestNum < 9) {
            ClientSendNext(upcall);
        } else {
            transport->CancelAllTimers();
        }
    };

    ClientSendNext(upcall);

    // Drop messages to or from replica 1
    transport->AddFilter(10, [](TransportReceiver *src, int srcIdx,
                                TransportReceiver *dst, int dstIdx,
                                Message &m, uint64_t &delay) {
                             if ((srcIdx == 1) || (dstIdx == 1)) {
                                 return false;
                             }
                             return true;
                         });

    transport->Run();

    // By now, they all should have executed the last request.
    for (int i = 0; i < config->n; i++) {
        EXPECT_EQ(10, ops[i].size());
        for (int j = 0; j < 10; j++) {
            EXPECT_EQ(RequestOp(j), ops[i][j]);
        }
    }
}


TEST_P(VRTest, FailedLeader)
{
    Client::continuation_t upcall = [&](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());

        if (requestNum == 5) {
            // Drop messages to or from replica 0
            transport->AddFilter(10, [](TransportReceiver *src, int srcIdx,
                                        TransportReceiver *dst, int dstIdx,
                                        Message &m, uint64_t &delay) {
                                     if ((srcIdx == 0) || (dstIdx == 0)) {
                                         return false;
                                     }
                                     return true;
                                 });
        }
        if (requestNum < 9) {
            ClientSendNext(upcall);
        } else {
            transport->CancelAllTimers();
        }
    };

    ClientSendNext(upcall);

    transport->Run();

    // By now, they all should have executed the last request.
    for (int i = 0; i < config->n; i++) {
        if (i == 0) {
            continue;
        }
        EXPECT_EQ(10, ops[i].size());
        for (int j = 0; j < 10; j++) {
            EXPECT_EQ(RequestOp(j), ops[i][j]);
        }
    }
}

TEST_P(VRTest, DroppedReply)
{
    bool received = false;
    Client::continuation_t upcall = [&](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());
        transport->CancelAllTimers();
        received = true;
    };

    // Drop the first ReplyMessage
    bool dropped = false;
    transport->AddFilter(10, [&dropped](TransportReceiver *src, int srcIdx,
                                        TransportReceiver *dst, int dstIdx,
                                        Message &m, uint64_t &delay) {
                             ReplyMessage r;
                             if (m.GetTypeName() == r.GetTypeName()) {
                                 if (!dropped) {
                                     dropped = true;
                                     return false;
                                 }
                             }
                             return true;
                         });
    ClientSendNext(upcall);

    transport->Run();

    EXPECT_TRUE(received);

    // Each replica should have executed only one request
    for (int i = 0; i < config->n; i++) {
        EXPECT_EQ(1, ops[i].size());
   }
}

TEST_P(VRTest, DroppedReplyThenFailedLeader)
{
    bool received = false;
    Client::continuation_t upcall = [&](const string &req, const string &reply) {
        EXPECT_EQ(req, LastRequestOp());
        EXPECT_EQ(reply, "reply: "+LastRequestOp());
        transport->CancelAllTimers();
        received = true;
    };

    // Drop the first ReplyMessage
    bool dropped = false;
    transport->AddFilter(10, [&dropped](TransportReceiver *src, int srcIdx,
                                        TransportReceiver *dst, int dstIdx,
                                        Message &m, uint64_t &delay) {
                             ReplyMessage r;
                             if (m.GetTypeName() == r.GetTypeName()) {
                                 if (!dropped) {
                                     dropped = true;
                                     return false;
                                 }
                             }
                             return true;
                         });

    // ...and after we've done that, fail the leader altogether
    transport->AddFilter(20, [&dropped](TransportReceiver *src, int srcIdx,
                                        TransportReceiver *dst, int dstIdx,
                                        Message &m, uint64_t &delay) {
                             if ((srcIdx == 0) || (dstIdx == 0)) {
                                 return !dropped;
                             }
                             return true;
                         });

    ClientSendNext(upcall);

    transport->Run();

    EXPECT_TRUE(received);

    // Each replica should have executed only one request
    // (and actually the faulty one should too, but don't check that)
    for (int i = 0; i < config->n; i++) {
        if (i != 0) {
            EXPECT_EQ(1, ops[i].size());
        }
    }
}

TEST_P(VRTest, ManyClients)
{
    const int NUM_CLIENTS = 10;
    const int MAX_REQS = 100;

    std::vector<VRClient *> clients;
    std::vector<int> lastReq;
    std::vector<Client::continuation_t> upcalls;
    for (int i = 0; i < NUM_CLIENTS; i++) {
        clients.push_back(new VRClient(*config, transport));
        lastReq.push_back(0);
        upcalls.push_back([&, i](const string &req, const string &reply) {
                EXPECT_EQ("reply: "+RequestOp(lastReq[i]), reply);
                lastReq[i] += 1;
                if (lastReq[i] < MAX_REQS) {
                    clients[i]->Invoke(RequestOp(lastReq[i]), upcalls[i]);
                }
            });
        clients[i]->Invoke(RequestOp(lastReq[i]), upcalls[i]);
    }

    // This could take a while; simulate two hours
    transport->Timer(7200000, [&]() {
            transport->CancelAllTimers();
        });

    transport->Run();

    for (int i = 0; i < config->n; i++) {
        ASSERT_EQ(NUM_CLIENTS * MAX_REQS, ops[i].size());
    }

    for (int i = 0; i < NUM_CLIENTS*MAX_REQS; i++) {
        for (int j = 0; j < config->n; j++) {
            ASSERT_EQ(ops[0][i], ops[j][i]);
        }
    }

    for (VRClient *c : clients) {
        delete c;
    }
}

TEST_P(VRTest, Stress)
{
    const int NUM_CLIENTS = 10;
    const int MAX_REQS = 100;
    const int MAX_DELAY = 1;
    const int DROP_PROBABILITY = 10; // 1/x

    std::vector<VRClient *> clients;
    std::vector<int> lastReq;
    std::vector<Client::continuation_t> upcalls;
    for (int i = 0; i < NUM_CLIENTS; i++) {
        clients.push_back(new VRClient(*config, transport));
        lastReq.push_back(0);
        upcalls.push_back([&, i](const string &req, const string &reply) {
                EXPECT_EQ("reply: "+RequestOp(lastReq[i]), reply);
                lastReq[i] += 1;
                if (lastReq[i] < MAX_REQS) {
                    clients[i]->Invoke(RequestOp(lastReq[i]), upcalls[i]);
                }
            });
        clients[i]->Invoke(RequestOp(lastReq[i]), upcalls[i]);
    }

    srand(time(NULL));

    // Delay messages from clients by a random amount, and drop some
    // of them
    transport->AddFilter(10, [=](TransportReceiver *src, int srcIdx,
                                TransportReceiver *dst, int dstIdx,
                                Message &m, uint64_t &delay) {
                             if (srcIdx == -1) {
                                 delay = rand() % MAX_DELAY;
                             }
                             return ((rand() % DROP_PROBABILITY) != 0);
                         });

    // This could take a while; simulate two hours
    transport->Timer(7200000, [&]() {
            transport->CancelAllTimers();
        });

    transport->Run();

    for (int i = 0; i < config->n; i++) {
        ASSERT_EQ(NUM_CLIENTS * MAX_REQS, ops[i].size());
    }

    for (int i = 0; i < NUM_CLIENTS*MAX_REQS; i++) {
        for (int j = 0; j < config->n; j++) {
            ASSERT_EQ(ops[0][i], ops[j][i]);
        }
    }

    for (VRClient *c : clients) {
        delete c;
    }
}

INSTANTIATE_TEST_CASE_P(Batching,
                        VRTest,
                        ::testing::Values(1, 8));
