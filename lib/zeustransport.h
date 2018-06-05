// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * zeustransport.h:
 *   message-passing network interface that uses ZEUS message delivery
 *   and libasync
 *
 * Copyright 2013 Dan R. K. Ports  <drkp@cs.washington.edu>
 * Copyright 2018 Irene Zhang <iyzhang@cs.washington.edu>
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

#ifndef _LIB_ZEUSTRANSPORT_H_
#define _LIB_ZEUSTRANSPORT_H_

#include "lib/configuration.h"
#include "lib/transport.h"
#include "lib/transportcommon.h"

#include "include/io-queue.h"

#include <event2/event.h>

#include <map>
#include <unordered_map>
#include <list>
#include <random>
#include <mutex>
#include <netinet/in.h>

class ZeusTransportAddress : public TransportAddress
{
public:
    ZeusTransportAddress * clone() const;
private:
    ZeusTransportAddress(const sockaddr_in &addr);
    
    sockaddr_in addr;
    friend class ZeusTransport;
    friend bool operator==(const ZeusTransportAddress &a,
                           const ZeusTransportAddress &b);
    friend bool operator!=(const ZeusTransportAddress &a,
                           const ZeusTransportAddress &b);
    friend bool operator<(const ZeusTransportAddress &a,
                          const ZeusTransportAddress &b);
};

class ZeusTransport : public TransportCommon<ZeusTransportAddress>
{
public:
    ZeusTransport(double dropRate = 0.0, double reogrderRate = 0.0,
                    int dscp = 0, bool handleSignals = true);
    virtual ~ZeusTransport();
    void Register(TransportReceiver *receiver,
                  const transport::Configuration &config,
                  int replicaIdx);
    void Run();
    void Stop();
    int Timer(uint64_t ms, timer_callback_t cb);
    bool CancelTimer(int id);
    void CancelAllTimers();
    
private:
    std::mutex mtx;
    struct ZeusTransportTimerInfo
    {
        ZeusTransport *transport;
        timer_callback_t cb;
        event *ev;
        int id;
    };
    struct ZeusTransportZeusListener
    {
        ZeusTransport *transport;
        TransportReceiver *receiver;
        int qd;
        int replicaIdx;
        event *ev;
    };
    event_base *libeventBase;
    std::vector<event *> listenerEvents;
    std::vector<event *> signalEvents;
    std::map<int, TransportReceiver*> receivers; // qd -> receiver
    std::map<TransportReceiver*, int> qds; // receiver -> qd
    int lastTimerId;
    std::map<int, ZeusTransportTimerInfo *> timers;
    std::map<ZeusTransportAddress, int> zeusOutgoing;
    std::map<struct ZeusTransportZeusListener *, ZeusTransportAddress *> zeusIncoming;
    
    bool SendMessageInternal(TransportReceiver *src,
                             const ZeusTransportAddress &dst,
                             const Message &m, bool multicast = false);

    ZeusTransportAddress
    LookupAddress(const transport::ReplicaAddress &addr);
    ZeusTransportAddress
    LookupAddress(const transport::Configuration &cfg,
                  int replicaIdx);
    const ZeusTransportAddress *
    LookupMulticastAddress(const transport::Configuration*config) { return NULL; };

    void ConnectZeus(TransportReceiver *src, const ZeusTransportAddress &dst);
    void OnTimer(ZeusTransportTimerInfo *info);
    static void TimerCallback(evutil_socket_t fd,
                              short what, void *arg);
    static void LogCallback(int severity, const char *msg);
    static void FatalCallback(int err);
    static void SignalCallback(evutil_socket_t fd,
                               short what, void *arg);
    static void ZeusAcceptCallback(evutil_socket_t fd, short what,
                                  void *arg);
    static void ZeusReadableCallback(evutil_socket_t fd, short what,
                                     void *arg);
};

#endif  // _LIB_ZEUSTRANSPORT_H_
