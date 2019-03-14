// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * dmtransport.h:
 *   message-passing network interface that uses DM message delivery
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

#ifndef _LIB_DMTRANSPORT_H_
#define _LIB_DMTRANSPORT_H_

#include "lib/configuration.h"
#include "lib/transport.h"
#include "lib/transportcommon.h"
#include "dmtr/libos.h"
#include "lib/latency.h"
#include <event2/event.h>

#include <map>
#include <list>
#include <random>
#include <mutex>
#include <netinet/in.h>
#include <signal.h>

#define MAX_CONNECTIONS 1000

class DmTransportAddress : public TransportAddress
{
public:
    DmTransportAddress * clone() const;
    DmTransportAddress();
private:
    DmTransportAddress(const sockaddr_in &addr);

    sockaddr_in addr;
    friend class DmTransport;
    friend bool operator==(const DmTransportAddress &a,
                           const DmTransportAddress &b);
    friend bool operator!=(const DmTransportAddress &a,
                           const DmTransportAddress &b);
    friend bool operator<(const DmTransportAddress &a,
                          const DmTransportAddress &b);
};

class DmTransport : public TransportCommon<DmTransportAddress>
{
public:
    DmTransport(double dropRate = 0.0, double reogrderRate = 0.0,
                    int dscp = 0, bool handleSignals = true);
    virtual ~DmTransport();
    void Register(TransportReceiver *receiver,
                  const transport::Configuration &config,
                  int replicaIdx);
    void Run();
    void Stop();
    int Timer(uint64_t ms, timer_callback_t cb);
    bool CancelTimer(int id);
    void CancelAllTimers();

private:
    int timerQD;
    int acceptQD;
    int replicaIdx;
    TransportReceiver *receiver;
     
    struct DmTransportTimerInfo
    {
        timer_callback_t cb;
        int id;
    };

    std::map<int, TransportReceiver*> receivers; // qd -> receiver
    //std::map<TransportReceiver*, int> qds; // receiver -> qd
    int lastTimerId;
    std::vector<dmtr_qtoken_t> tokens;
    std::map<int, DmTransportTimerInfo *> timers;
    std::map<DmTransportAddress, int> dmOutgoing;
    std::map<int, DmTransportAddress> dmIncoming;

    bool SendMessageInternal(TransportReceiver *src,
                             const DmTransportAddress &dst,
                             const Message &m, bool multicast = false);

    DmTransportAddress
    LookupAddress(const transport::ReplicaAddress &addr);
    DmTransportAddress
    LookupAddress(const transport::Configuration &cfg,
                  int replicaIdx);
    const DmTransportAddress *
    LookupMulticastAddress(const transport::Configuration*config) { return NULL; };

    void ConnectDm(TransportReceiver *src, const DmTransportAddress &dst);
    void OnTimer(DmTransportTimerInfo *info);
    void TimerCallback(DmTransportTimerInfo *info);
    void DmAcceptCallback(dmtr_accept_result ares);
    void DmPopCallback(int qd, TransportReceiver *receiver, dmtr_sgarray_t &sga);
    void CloseConn(int qd);
};

#endif  // _LIB_DMTRANSPORT_H_
