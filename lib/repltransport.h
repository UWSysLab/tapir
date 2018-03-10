// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * repltransport.h: REPL-driven step-by-step simulated transport.
 *
 * Copyright 2013-2015 Irene Zhang <iyzhang@cs.washington.edu>
 *                     Naveen Kr. Sharma <naveenks@cs.washington.edu>
 *                     Dan R. K. Ports  <drkp@cs.washington.edu>
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

// Distributed algorithms have to handle arbitrary message delays, message
// loss, message reordering, node failure, network partitions, etc. However,
// these failure scenarios are rare, which can make it difficult to flesh out
// all the corner cases of a distributed algorithm.
//
// Take IR for example. If we want to trigger the IR-MERGE-RECORDS function to
// run with a non-empty d and a non-empty u, we have to
//   1. propose two separate messages,
//   2. deliver one to a supermajority,
//   3. deliver the other to a simple majority,
//   4. prevent both messages from being finalized, and
//   5. trigger a view change.
//
// ReplTransport is a simulated transport, like SimulatedTransport, that lets
// users manipulate every aspect of the execution of a distributed system. When
// run, a ReplTransport opens up a REPL with which users can use to trigger an
// arbitrary timeout or deliver an arbitrary message to a receiver.
//
// For example, imagine a simple distributed system with two nodes: ping
// (localhost:8000) and pong (localhost:9000). Initially, ping sends a message
// to pong, pong replies with a message, ping replies with another message, and
// so on. If a node hasn't heard from the other after some timeout, it resends
// its message. An interaction with a ReplTransport would look something like
// this (comments inline):
//
//     $ ./ping_pong
//     > show                  # show the state
//     - History               # A history of all commands (empty at first)
//     - Timers                # A list of all timer ids
//       - [1]                 # ping's timeout
//       - [2]                 # pong's timeout
//     - localhost:8000        # ping (no pending messages)
//     - localhost:9000        # pong
//       - [0] PingMessage     # pong's pending message from ping
//
//     > localhost 9000 0      # Deliver the 0th message to pong
//     > show
//     - History               # A history of all executed commands
//         transport.DeliverMessage({"localhost", "9000"}, 0);
//     - Timers
//       - [1]
//       - [2]
//     - localhost:8000
//       - [0] PongMessage     # pings's pending message from pong
//     - localhost:9000
//       - [0] PingMessage     # Notice that this message wasn't removed. We
//                             # can deliver the same message multiple times.
//
//     > localhost 8000 0      # Deliver the 0th message to ping
//     > show
//     - History
//         transport.DeliverMessage({"localhost", "9000"}, 0);
//         transport.DeliverMessage({"localhost", "8000"}, 0);
//     - Timers
//       - [1]
//       - [2]
//     - localhost:8000
//       - [0] PongMessage
//     - localhost:9000
//       - [0] PingMessage
//       - [1] PingMessage
//
//     > 1                     # Trigger ping's timeout
//     > show
//     - History
//         transport.DeliverMessage({"localhost", "9000"}, 0);
//         transport.DeliverMessage({"localhost", "8000"}, 0);
//         transport.TriggerTimer(1);
//     - Timers
//       - [1]
//       - [2]
//     - localhost:8000
//       - [0] PongMessage
//     - localhost:9000
//       - [0] PingMessage
//       - [1] PingMessage
//       - [2] PingMessage     # ping resent its message to pong
//
//     > quit
//
// Also notice that the ReplTransport prints out a history of the executed
// commands. You can copy and paste these commands into your code to replay
// your interaction with the REPL.

#ifndef _LIB_REPLTRANSPORT_H_
#define _LIB_REPLTRANSPORT_H_

#include <functional>
#include <map>
#include <memory>
#include <ostream>
#include <string>
#include <tuple>

#include "lib/configuration.h"
#include "lib/transport.h"
#include "lib/transportcommon.h"

class ReplTransportAddress : public TransportAddress {
public:
    // Constructors.
    ReplTransportAddress() {}

    ReplTransportAddress(std::string host, std::string port)
        : host_(std::move(host)), port_(std::move(port)) {}

    ReplTransportAddress(const ReplTransportAddress &other)
        : ReplTransportAddress(other.host_, other.port_) {}

    ReplTransportAddress(ReplTransportAddress &&other)
        : ReplTransportAddress() {
        swap(*this, other);
    }

    ReplTransportAddress &operator=(ReplTransportAddress other) {
        swap(*this, other);
        return *this;
    }

    friend void swap(ReplTransportAddress &x, ReplTransportAddress &y) {
        std::swap(x.host_, y.host_);
        std::swap(x.port_, y.port_);
    }

    // Comparators.
    bool operator==(const ReplTransportAddress &other) const {
        return Key() == other.Key();
    }
    bool operator!=(const ReplTransportAddress &other) const {
        return Key() != other.Key();
    }
    bool operator<(const ReplTransportAddress &other) const {
        return Key() < other.Key();
    }
    bool operator<=(const ReplTransportAddress &other) const {
        return Key() <= other.Key();
    }
    bool operator>(const ReplTransportAddress &other) const {
        return Key() > other.Key();
    }
    bool operator>=(const ReplTransportAddress &other) const {
        return Key() >= other.Key();
    }

    // Getters.
    const std::string& Host() const {
        return host_;
    }

    const std::string& Port() const {
        return port_;
    }

    ReplTransportAddress *clone() const override {
        return new ReplTransportAddress(host_, port_);
    }

    friend std::ostream &operator<<(std::ostream &out,
                                    const ReplTransportAddress &addr) {
        out << addr.host_ << ":" << addr.port_;
        return out;
    }

private:
    std::tuple<const std::string&, const std::string&> Key() const {
        return std::forward_as_tuple(host_, port_);
    }

    std::string host_;
    std::string port_;
};

class ReplTransport : public TransportCommon<ReplTransportAddress> {
public:
    void Register(TransportReceiver *receiver,
                  const transport::Configuration &config,
                  int replicaIdx) override;
    int Timer(uint64_t ms, timer_callback_t cb) override;
    bool CancelTimer(int id) override;
    void CancelAllTimers() override;

    // DeliverMessage(addr, i) delivers the ith queued inbound message to the
    // receiver with address addr. It's possible to send a message to the
    // address of a receiver that hasn't yet registered. In this case,
    // DeliverMessage returns false. Otherwise, it returns true.
    bool DeliverMessage(const ReplTransportAddress& addr, int index);

    // Run timer with id timer_id.
    void TriggerTimer(int timer_id);

    // Launch the REPL.
    void Run();

protected:
    bool SendMessageInternal(TransportReceiver *src,
                             const ReplTransportAddress &dst, const Message &m,
                             bool multicast = false) override;
    ReplTransportAddress LookupAddress(const transport::Configuration &cfg,
                                       int replicaIdx) override;
    const ReplTransportAddress *LookupMulticastAddress(
        const transport::Configuration *cfg) override;

private:
    // Prompt the user for input and either (1) trigger a timer, (2) deliver a
    // message, or (3) quit. RunOne returns true if the user decides to quit.
    bool RunOne();

    // Pretty print the current state of the system. For example, PrintState
    // prints the queued messages for every node in the system.
    void PrintState() const;

    struct QueuedMessage {
        ReplTransportAddress src;
        std::unique_ptr<Message> msg;

        QueuedMessage(ReplTransportAddress src, std::unique_ptr<Message> msg)
            : src(std::move(src)), msg(std::move(msg)) {}
    };

    struct TransportReceiverState {
        // receiver can be null if it has queued messages but hasn't yet been
        // registered with a ReplTransport.
        TransportReceiver *receiver;

        // Queued inbound messages.
        std::vector<QueuedMessage> msgs;
    };

    // receivers_ maps a receiver r's address to r and r's queued messages.
    std::map<ReplTransportAddress, TransportReceiverState> receivers_;

    // timer_id_ is an incrementing counter used to assign timer ids.
    int timer_id_ = 0;

    // timers_ maps timer ids to timers.
    std::map<int, timer_callback_t> timers_;

    // client_id_ is an incrementing counter used to assign addresses to
    // clients. The first client gets address client:0, the next client gets
    // address client:1, etc.
    int client_id_ = 0;

    // A history of all the command issued to this ReplTransport.
    std::vector<std::string> history_;
};

#endif // _LIB_REPLTRANSPORT_H_
