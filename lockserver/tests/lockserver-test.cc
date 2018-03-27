// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * lockserver_test.cc:
 *   test cases for lock server
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
#include <fstream>
#include <memory>
#include <thread>

#include <gtest/gtest.h>

#include "lib/configuration.h"
#include "lib/repltransport.h"
#include "lockserver/client.h"
#include "lockserver/server.h"
#include "replication/ir/replica.h"

class LockServerTest : public testing::Test {
protected:
    std::vector<transport::ReplicaAddress> replica_addrs_;
    std::unique_ptr<transport::Configuration> config_;
    ReplTransport transport_;
    std::vector<std::unique_ptr<lockserver::LockClient>> clients_;
    std::vector<std::unique_ptr<lockserver::LockServer>> servers_;
    std::vector<std::unique_ptr<replication::ir::IRReplica>> replicas_;

    LockServerTest() {
        replica_addrs_ = {{"replica", "0"},
                          {"replica", "1"},
                          {"replica", "2"},
                          {"replica", "3"},
                          {"replica", "4"}};
        config_ = std::unique_ptr<transport::Configuration>(
            new transport::Configuration(5, 2, replica_addrs_));
        RemovePersistedFiles();

        for (std::size_t i = 0; i < 3; ++i) {
            auto client = std::unique_ptr<lockserver::LockClient>(
                new lockserver::LockClient(&transport_, *config_));
            client->lock_async(std::to_string(i));
            clients_.push_back(std::move(client));
        }

        for (std::size_t i = 0; i < replica_addrs_.size(); ++i) {
            auto server = std::unique_ptr<lockserver::LockServer>(
                new lockserver::LockServer());
            servers_.push_back(std::move(server));
            auto replica = std::unique_ptr<replication::ir::IRReplica>(
                new replication::ir::IRReplica(*config_, i, &transport_,
                                               servers_[i].get()));
            replicas_.push_back(std::move(replica));
        }
    }

    virtual void TearDown() {
        RemovePersistedFiles();
    }

    virtual void RemovePersistedFiles() {
        for (std::size_t i = 0; i < replica_addrs_.size(); ++i) {
            const transport::ReplicaAddress &addr = replica_addrs_[i];
            const std::string filename =
                addr.host + ":" + addr.port + "_" + std::to_string(i) + ".bin";
            std::ifstream f(filename);
            if (f.good()) {
                int success = std::remove(filename.c_str());
                ASSERT(success == 0);
            }
        }
    }
};

// Note that these tests are all white box smoke tests. They depend on the
// low-level details of knowing exactly which timeouts are registered and which
// messages are sent. If an implementation detail is changed to make some of
// these tests fail, you should cal transport_.Run() and walk through the
// execution to trigger the desired behavior. Also, they only check to make
// sure that nothing crashes, though you can read through the Debug prints to
// make sure everything looks right.
//
// TODO: Use a ReplTransport for tests like the ones in ir-test.cc to assert
// that the correct messages are being sent.

TEST_F(LockServerTest, SuccessfulFastPathLock) {
    // Send client 0's lock request.
    transport_.TriggerTimer(1);

    // Deliver lock request to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 0);
    }

    // Deliver lock reply to client.
    for (std::size_t i = 0; i < replica_addrs_.size(); ++i) {
        transport_.DeliverMessage({"client", "0"}, i);
    }

    // Deliver finalize to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 1);
    }

    // Deliver confirm to client.
    int j = replica_addrs_.size();
    for (std::size_t i = j; i < j + replica_addrs_.size(); ++i) {
        transport_.DeliverMessage({"client", "0"}, i);
    }
}

TEST_F(LockServerTest, SuccessfulSlowPathLock) {
    // Send client 0's lock request.
    transport_.TriggerTimer(1);

    // Transition to slow path.
    transport_.TriggerTimer(clients_.size() + replica_addrs_.size() + 1);

    // Deliver lock request to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 0);
    }

    // Deliver lock reply to client.
    for (std::size_t i = 0; i < replica_addrs_.size(); ++i) {
        transport_.DeliverMessage({"client", "0"}, i);
    }

    // Deliver finalize to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 1);
    }

    // Deliver confirm to client.
    int j = replica_addrs_.size();
    for (std::size_t i = j; i < j + replica_addrs_.size(); ++i) {
        transport_.DeliverMessage({"client", "0"}, i);
    }
}

TEST_F(LockServerTest, SuccessfulViewChange) {
    // Send client 0's lock request.
    transport_.TriggerTimer(1);

    // Deliver lock request to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 0);
    }

    // Initiate view changes on all replicas.
    const std::size_t nclients = clients_.size();
    const std::size_t nreplicas = replica_addrs_.size();
    for (std::size_t i = nclients + 1; i < nclients + nreplicas + 1; ++i) {
        transport_.TriggerTimer(i);
    }

    // Deliver DoViewChangeMessages to new primary.
    const transport::ReplicaAddress& primary = replica_addrs_[1];
    for (std::size_t i = 1; i < 1 + nreplicas - 1; ++i) {
        transport_.DeliverMessage({primary.host, primary.port}, i);
    }

    // Deliver StartViewMessage to all replicas.
    for (std::size_t i = 0; i < nreplicas; ++i) {
        if (i == 1) {
            continue;
        }
        const transport::ReplicaAddress& addr = replica_addrs_[i];
        transport_.DeliverMessage({addr.host, addr.port}, nreplicas);
    }
}

TEST_F(LockServerTest, SuccessfulViewChangeNonemptyRdu) {
    const std::size_t nclients = clients_.size();
    const std::size_t nreplicas = replica_addrs_.size();
    ASSERT_GE(nclients, 3);
    ASSERT_GE(nreplicas, 3);

    // Send client 0's lock request.
    transport_.TriggerTimer(1);

    // Deliver lock request to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 0);
    }

    // Deliver lock reply to client.
    for (std::size_t i = 0; i < replica_addrs_.size(); ++i) {
        transport_.DeliverMessage({"client", "0"}, i);
    }

    // Deliver finalize to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 1);
    }

    // Send client 1's lock request.
    transport_.TriggerTimer(2);

    // Deliver lock request to first three replicas.
    for (std::size_t i = 0; i < 3; ++i) {
        const transport::ReplicaAddress &addr = replica_addrs_[i];
        transport_.DeliverMessage({addr.host, addr.port}, 2);
    }

    // Send client 2's lock request.
    transport_.TriggerTimer(3);

    // Deliver lock request to first replica.
    const transport::ReplicaAddress &addr = replica_addrs_[0];
    transport_.DeliverMessage({addr.host, addr.port}, 3);

    // View change first three replicas.
    for (std::size_t i = nclients + 1; i < nclients + 1 + 3; ++i) {
        transport_.TriggerTimer(i);
    }

    // Deliver DoViewChangeMessages to new primary.
    const transport::ReplicaAddress& primary = replica_addrs_[1];
    for (std::size_t i = 4; i < 4 + 2; ++i) {
        transport_.DeliverMessage({primary.host, primary.port}, i);
    }

    // Deliver StartViewMessage to replica 0 and 2.
    const transport::ReplicaAddress& addr0 = replica_addrs_[0];
    const transport::ReplicaAddress& addr2 = replica_addrs_[2];
    transport_.DeliverMessage({addr0.host, addr0.port}, 6);
    transport_.DeliverMessage({addr2.host, addr2.port}, 6);
}

TEST_F(LockServerTest, FinalizeConsensusReply) {
    const std::size_t nclients = clients_.size();
    const std::size_t nreplicas = replica_addrs_.size();

    // Send client 0's lock request.
    transport_.TriggerTimer(1);

    // Deliver lock request to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 0);
    }

    // Trigger view change.
    for (std::size_t i = nclients + 1; i < nclients + 1 + nreplicas; ++i) {
        transport_.TriggerTimer(i);
    }

    // Deliver DoViewChangeMessages to new primary.
    const transport::ReplicaAddress& primary = replica_addrs_[1];
    for (std::size_t i = 1; i < 1 + nreplicas - 1; ++i) {
        transport_.DeliverMessage({primary.host, primary.port}, i);
    }

    // Deliver StartViewMessage to all replicas.
    for (std::size_t i = 0; i < nreplicas; ++i) {
        if (i == 1) {
            continue;
        }
        const transport::ReplicaAddress& addr = replica_addrs_[i];
        transport_.DeliverMessage({addr.host, addr.port}, nreplicas);
    }

    // Deliver lock request to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 0);
    }

    // Deliver finalized reply to client.
    transport_.DeliverMessage({"client", "0"}, nreplicas);
}

TEST_F(LockServerTest, MismatchedConsensus) {
    const std::size_t nclients = clients_.size();
    const std::size_t nreplicas = replica_addrs_.size();

    // Send client 0's lock request.
    transport_.TriggerTimer(1);

    // Transition to slow path.
    transport_.TriggerTimer(nclients + nreplicas + 1);

    // Deliver lock request to replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 0);
    }

    // Deliver lock reply to client.
    for (std::size_t i = 0; i < replica_addrs_.size(); ++i) {
        transport_.DeliverMessage({"client", "0"}, i);
    }

    // Trigger view change.
    for (std::size_t i = nclients + 1; i < nclients + 1 + nreplicas; ++i) {
        transport_.TriggerTimer(i);
    }

    // Deliver DoViewChangeMessages to new primary.
    const transport::ReplicaAddress& primary = replica_addrs_[1];
    for (std::size_t i = 2; i < 2 + nreplicas - 1; ++i) {
        transport_.DeliverMessage({primary.host, primary.port}, i);
    }

    // Deliver StartViewMessage to all replicas.
    for (std::size_t i = 0; i < nreplicas; ++i) {
        if (i == 1) {
            continue;
        }
        const transport::ReplicaAddress& addr = replica_addrs_[i];
        transport_.DeliverMessage({addr.host, addr.port}, 2 + nreplicas - 1);
    }

    // Deliver FinalizeConsensusMessage to all replicas.
    for (const auto &addr : replica_addrs_) {
        transport_.DeliverMessage({addr.host, addr.port}, 1);
    }

    // Deliver ConfirmMessages to client 0.
    for (std::size_t i = nreplicas; i < nreplicas + nreplicas; ++i) {
        transport_.DeliverMessage({"client", "0"}, i);
    }
}
