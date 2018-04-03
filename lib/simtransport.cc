// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * simtransport.cc:
 *   simulated message-passing interface for testing use
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

#include "lib/assert.h"
#include "lib/message.h"
#include "lib/simtransport.h"
#include <google/protobuf/message.h>

SimulatedTransportAddress::SimulatedTransportAddress(int addr)
    : addr(addr)
{

}

int
SimulatedTransportAddress::GetAddr() const
{
    return addr;
}

SimulatedTransportAddress *
SimulatedTransportAddress::clone() const
{
    SimulatedTransportAddress *c = new SimulatedTransportAddress(addr);
    return c;
}

bool
SimulatedTransportAddress::operator==(const SimulatedTransportAddress &other) const
{
    return addr == other.addr;
}

SimulatedTransport::SimulatedTransport()
{
    lastAddr = -1;
    lastTimerId = 0;
    vtime = 0;
    processTimers = true;
}

SimulatedTransport::~SimulatedTransport()
{

}

void
SimulatedTransport::Register(TransportReceiver *receiver,
                             const transport::Configuration &config,
                             int replicaIdx)
{
    // Allocate an endpoint
    ++lastAddr;
    int addr = lastAddr;
    endpoints[addr] = receiver;

    // Tell the receiver its address
    receiver->SetAddress(new SimulatedTransportAddress(addr));

    RegisterConfiguration(receiver, config, replicaIdx);

    // If this is registered as a replica, record the index
    replicaIdxs[addr] = replicaIdx;
}

bool
SimulatedTransport::SendMessageInternal(TransportReceiver *src,
                                        const SimulatedTransportAddress &dstAddr,
                                        const Message &m,
                                        bool multicast)
{
    ASSERT(!multicast);

    int dst = dstAddr.addr;

    Message *msg = m.New();
    msg->CheckTypeAndMergeFrom(m);

    int srcAddr =
        dynamic_cast<const SimulatedTransportAddress &>(src->GetAddress()).addr;

    uint64_t delay = 0;
    for (auto f : filters) {
        if (!f.second(src, replicaIdxs[srcAddr],
                      endpoints[dst], replicaIdxs[dst],
                      *msg, delay)) {
            // Message dropped by filter
            // XXX Should we return failure?
            delete msg;
            return true;
        }
    }

    string msgData;
    msg->SerializeToString(&msgData);
    delete msg;

    QueuedMessage q(dst, srcAddr, m.GetTypeName(), msgData);

    if (delay == 0) {
        queue.push_back(q);
    } else {
        Timer(delay, [=]() {
                queue.push_back(q);
            });
    }
    return true;
}

SimulatedTransportAddress
SimulatedTransport::LookupAddress(const transport::Configuration &cfg,
                                  int idx)
{
    // Check every registered replica to see if its configuration and
    // idx match. This is the least efficient possible way to do this,
    // but that's why this is the simulated transport not the real
    // one... (And we only have to do this once at runtime.)


    for (auto & kv : configurations) {
        if (*(kv.second) == cfg) {
            // Configuration matches. Does the index?
            const SimulatedTransportAddress &addr =
                dynamic_cast<const SimulatedTransportAddress&>(kv.first->GetAddress());
            if (replicaIdxs[addr.addr] == idx) {
                // Matches.
                return addr;
            }
        }
    }

    Panic("No replica %d was registered", idx);
}

const SimulatedTransportAddress *
SimulatedTransport::LookupMulticastAddress(const transport::Configuration *cfg)
{
    return NULL;
}

void
SimulatedTransport::Run()
{
    LookupAddresses();

    do {
        // Process queue
        while (!queue.empty()) {
            QueuedMessage &q = queue.front();
            TransportReceiver *dst = endpoints[q.dst];
            dst->ReceiveMessage(SimulatedTransportAddress(q.src), q.type, q.msg);
            queue.pop_front();
        }

        // If there's a timer, deliver the earliest one only
        if (processTimers && !timers.empty()) {
            auto iter = timers.begin();
            ASSERT(iter->second.when >= vtime);
            vtime = iter->second.when;
            timer_callback_t cb = iter->second.cb;
            timers.erase(iter);
            cb();
        }

        // ...then retry to see if there are more queued messages to
        // deliver first
    } while (!queue.empty() || (processTimers && !timers.empty()));
}

void
SimulatedTransport::AddFilter(int id, filter_t filter)
{
    filters.insert(std::pair<int,filter_t>(id, filter));
}

void
SimulatedTransport::RemoveFilter(int id)
{
    filters.erase(id);
}


int
SimulatedTransport::Timer(uint64_t ms, timer_callback_t cb)
{
    ++lastTimerId;
    int id = lastTimerId;
    PendingTimer t;
    t.when = vtime + ms;
    t.cb = cb;
    t.id = id;
    timers.insert(std::pair<uint64_t, PendingTimer>(t.when, t));
    return id;
}

bool
SimulatedTransport::CancelTimer(int id)
{
    bool found = false;
    for (auto iter = timers.begin(); iter != timers.end();) {
        if (iter->second.id == id) {
            found = true;
            iter = timers.erase(iter);
        } else {
            iter++;
        }
    }

    return found;
}

void
SimulatedTransport::CancelAllTimers()
{
    timers.clear();
    processTimers = false;
}
