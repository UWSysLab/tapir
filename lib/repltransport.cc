// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * repltransport.cc: REPL-driven step-by-step simulated transport.
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
#include "lib/repltransport.h"

#include <iostream>
#include <iterator>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>

namespace {

// https://stackoverflow.com/a/236803/3187068
template <typename Out>
void split(const std::string &s, char delim, Out result) {
    std::stringstream ss(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
        *(result++) = item;
    }
}

// https://stackoverflow.com/a/236803/3187068
std::vector<std::string> split(const std::string &s, char delim) {
    std::vector<std::string> elems;
    split(s, delim, std::back_inserter(elems));
    return elems;
}

// https://stackoverflow.com/a/4654718/3187068
bool is_number(const std::string &s) {
    std::string::const_iterator it = s.begin();
    while (it != s.end() && std::isdigit(*it)) ++it;
    return !s.empty() && it == s.end();
}

// https://stackoverflow.com/a/1494435/3187068
void string_replace(std::string *str, const std::string &oldStr,
                    const std::string &newStr) {
    std::string::size_type pos = 0u;
    while ((pos = str->find(oldStr, pos)) != std::string::npos) {
        str->replace(pos, oldStr.length(), newStr);
        pos += newStr.length();
    }
}

}  // namespace

void ReplTransport::Register(TransportReceiver *receiver,
                             const transport::Configuration &config,
                             int replicaIdx) {
    // If replicaIdx is -1, then the registering receiver is a client.
    // Otherwise, replicaIdx is in the range [0, config.n), and the registering
    // receiver is a replica.
    bool is_client = replicaIdx == -1;

    if (is_client) {
        // Create the client's address.
        std::string port = std::to_string(client_id_);
        auto repl_addr = new ReplTransportAddress("client", std::move(port));
        receiver->SetAddress(repl_addr);
        client_id_++;

        // Register receiver.
        receivers_[*repl_addr].receiver = receiver;
    } else {
        // Set the receiver's address.
        transport::ReplicaAddress addr = config.replica(replicaIdx);
        auto repl_addr = new ReplTransportAddress(addr.host, addr.port);
        receiver->SetAddress(repl_addr);

        // Register receiver.
        receivers_[*repl_addr].receiver = receiver;
    }

    // Register with superclass.
    RegisterConfiguration(receiver, config, replicaIdx);
}

int ReplTransport::Timer(uint64_t ms, timer_callback_t cb) {
    timer_id_++;
    ASSERT(timers_.count(timer_id_) == 0);
    timers_[timer_id_] = cb;
    return timer_id_;
}

bool ReplTransport::CancelTimer(int id) {
    if (timers_.count(id) == 0) {
        return false;
    } else {
        timers_.erase(id);
        return true;
    }
}

void ReplTransport::CancelAllTimers() {
    timers_.clear();
}

bool ReplTransport::DeliverMessage(const ReplTransportAddress &addr,
                                   int index) {
    history_.push_back("transport.DeliverMessage({\"" + addr.Host() + "\", \"" +
                       addr.Port() + "\"}, " + std::to_string(index) + ");");
    ASSERT(receivers_.count(addr) != 0);
    TransportReceiverState &state = receivers_[addr];

    // If the recipient of this address hasn't yet been registered, then
    // state.receiver is null.
    if (state.receiver == nullptr) {
        return false;
    }

    // Deliver the message.
    const QueuedMessage &m = state.msgs.at(index);
    string data;
    m.msg->SerializeToString(&data);
    state.receiver->ReceiveMessage(m.src, m.msg->GetTypeName(), data);
    return true;
}

void ReplTransport::TriggerTimer(int timer_id) {
    history_.push_back("transport.TriggerTimer(" + std::to_string(timer_id) +
                       ");");
    ASSERT(timers_.count(timer_id) != 0);
    timers_[timer_id]();
}

void ReplTransport::PrintState() const {
    // Show the history.
    std::cout << "- History" << std::endl;
    for (const std::string &command : history_) {
        std::cout << "    " << command << std::endl;
    }

    // Show the timers.
    std::cout << "- Timers" << std::endl;
    for (const std::pair<const int, timer_callback_t> &p : timers_) {
        std::cout << "  - [" << p.first << "]" << std::endl;
    }

    // Show the message buffers.
    for (const std::pair<const ReplTransportAddress, TransportReceiverState>
             &p : receivers_) {
        const ReplTransportAddress &addr = p.first;
        const TransportReceiverState &state = p.second;

        std::cout << "- " << addr;
        if (state.receiver == nullptr) {
            std::cout << " [not registered]";
        }
        std::cout << std::endl;

        for (std::size_t i = 0; i < state.msgs.size(); ++i) {
            const Message *msg = state.msgs[i].msg.get();
            std::string debug = msg->DebugString();
            string_replace(&debug, "\n", "\n        ");
            std::cout << "  - [" << i << "] " << msg->GetTypeName() << std::endl
                      << "        " << debug << std::endl;
        }
    }
}

bool ReplTransport::RunOne() {
    // Parse response.
    while (true) {
        // Prompt user and read response.
        std::cout << "> " << std::flush;
        std::string line;
        std::getline(std::cin, line);
        if (std::cin.fail() || std::cin.eof()) {
            return true;
        }
        std::vector<std::string> words = split(line, ' ');

        const std::string usage =
            "Usage: quit | show | <timer_id> | <host> <port> <index>";
        if (words.size() == 1) {
            if (words[0] == "quit") {
                return true;
            }
            if (words[0] == "show") {
                PrintState();
                return false;
            }

            if (is_number(words[0])) {
                int timer_id = std::stoi(words[0]);
                TriggerTimer(timer_id);
                return false;
            } else {
                std::cout << usage << std::endl;
            }
        } else if (words.size() == 3) {
            if (!is_number(words[2])) {
                std::cout << usage << std::endl;
            } else {
                ReplTransportAddress addr(words[0], words[1]);
                int index = std::stoi(words[2]);
                if (receivers_.count(addr) == 0) {
                    std::cout << "Receiver not found." << std::endl;
                } else {
                    DeliverMessage(addr, index);
                    return false;
                }
            }
        } else {
            std::cout << usage << std::endl;
        }
    }
}

void ReplTransport::Run() {
    bool done = false;
    while (!done) {
        done = RunOne();
    }
}

bool ReplTransport::SendMessageInternal(TransportReceiver *src,
                                        const ReplTransportAddress &dst,
                                        const Message &m,
                                        bool multicast) {
    // Multicast is not supported.
    ASSERT(!multicast);

    const ReplTransportAddress &repl_addr =
        dynamic_cast<const ReplTransportAddress &>(src->GetAddress());
    std::unique_ptr<Message> msg(m.New());
    msg->CheckTypeAndMergeFrom(m);
    receivers_[dst].msgs.push_back(QueuedMessage(repl_addr, std::move(msg)));
    return true;
}

ReplTransportAddress ReplTransport::LookupAddress(
    const transport::Configuration &cfg, int replicaIdx) {
    transport::ReplicaAddress addr = cfg.replica(replicaIdx);
    return ReplTransportAddress(addr.host, addr.port);
}

const ReplTransportAddress *ReplTransport::LookupMulticastAddress(
    const transport::Configuration *cfg) {
    return nullptr;
}
