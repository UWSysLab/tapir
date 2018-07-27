// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * zeustransport.cc:
 *   message-passing network interface that uses ZEUS message delivery
 *   and libasync
 *
 * Copyright 2013 Dan R. K. Ports  <drkp@cs.washington.edu>
 * Copyright 2018 Irene Zhang  <iyzhang@cs.washington.edu>
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
#include "lib/configuration.h"
#include "lib/message.h"
#include "lib/zeustransport.h"

#include <google/protobuf/message.h>
#include <event2/thread.h>

#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <netinet/in.h>

#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <netdb.h>
#include <functional>

const size_t MAX_Zeus_SIZE = 100; // XXX
const uint32_t MAGIC = 0x06121983;
static bool stopLoop = false;

using std::make_pair;
using Zeus::sgarray;
using Zeus::qtoken;

ZeusTransportAddress::ZeusTransportAddress(const sockaddr_in &addr)
    : addr(addr)
{
    memset((void *)addr.sin_zero, 0, sizeof(addr.sin_zero));
}

ZeusTransportAddress *
ZeusTransportAddress::clone() const
{
    ZeusTransportAddress *c = new ZeusTransportAddress(*this);
    return c;    
}

bool operator==(const ZeusTransportAddress &a, const ZeusTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) == 0);
}

bool operator!=(const ZeusTransportAddress &a, const ZeusTransportAddress &b)
{
    return !(a == b);
}

bool operator<(const ZeusTransportAddress &a, const ZeusTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) < 0);
}

ZeusTransportAddress
ZeusTransport::LookupAddress(const transport::ReplicaAddress &addr)
{
        int res;
        struct addrinfo hints;
        memset(&hints, 0, sizeof(hints));
        hints.ai_family   = AF_INET;
        hints.ai_socktype = SOCK_STREAM;
        hints.ai_protocol = 0;
        hints.ai_flags    = 0;
        struct addrinfo *ai;
        if ((res = getaddrinfo(addr.host.c_str(),
                               addr.port.c_str(),
                               &hints, &ai))) {
            Panic("Failed to resolve %s:%s: %s",
                  addr.host.c_str(), addr.port.c_str(), gai_strerror(res));
        }
        if (ai->ai_addr->sa_family != AF_INET) {
            Panic("getaddrinfo returned a non IPv4 address");
        }
        ZeusTransportAddress out =
            ZeusTransportAddress(*((sockaddr_in *)ai->ai_addr));
        freeaddrinfo(ai);
        return out;
}

ZeusTransportAddress
ZeusTransport::LookupAddress(const transport::Configuration &config,
                            int idx)
{
    const transport::ReplicaAddress &addr = config.replica(idx);
    return LookupAddress(addr);
}

static void
BindToPort(int qd, const string &host, const string &port)
{
    struct sockaddr_in sin;

    // look up its hostname and port number (which
    // might be a service name)
    struct addrinfo hints;
    hints.ai_family   = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = 0;
    hints.ai_flags    = AI_PASSIVE;
    struct addrinfo *ai;
    int res;
    if ((res = getaddrinfo(host.c_str(),
                           port.c_str(),
                           &hints, &ai))) {
        Panic("Failed to resolve host/port %s:%s: %s",
              host.c_str(), port.c_str(), gai_strerror(res));
    }
    ASSERT(ai->ai_family == AF_INET);
    ASSERT(ai->ai_socktype == SOCK_STREAM);
    if (ai->ai_addr->sa_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");        
    }
    sin = *(sockaddr_in *)ai->ai_addr;
    freeaddrinfo(ai);
    Debug("Binding to %s %d Zeus", inet_ntoa(sin.sin_addr), htons(sin.sin_port));

    if (Zeus::bind(qd, (sockaddr *)&sin, sizeof(sin)) < 0) {
        PPanic("Failed to bind to socket");
    }


}

ZeusTransport::ZeusTransport(double dropRate, double reorderRate,
			   int dscp, bool handleSignals)
{
    lastTimerId = 0;
    
    // Set up signal handler
    if (handleSignals) {
        struct sigaction sa;
        // Setup the sighub handler
        sa.sa_handler = &ZeusSignalCallback;
        // Restart the system call, if at all possible
        sa.sa_flags = SA_RESTART;

        // Block every signal during the handler
        sigfillset(&sa.sa_mask);

        // Intercept SIGHUP and SIGINT
        if (sigaction(SIGTERM, &sa, NULL) == -1) {
            Panic("Cannot handle SIGTERM");
        }

        if (sigaction(SIGINT, &sa, NULL) == -1) {
            Panic("Error: cannot handle SIGINT"); // Should not happen
        }
    }
    Debug("Using Zeus transport");
}

ZeusTransport::~ZeusTransport()
{
    // XXX Shut down libevent?

    // for (auto kv : timers) {
    //     delete kv.second;
    // }
}

void
ZeusTransport::ConnectZeus(TransportReceiver *src, const ZeusTransportAddress &dst)
{
    // Create socket
    int qd;
    if ((qd = Zeus::socket(AF_INET, SOCK_STREAM, 0)) < 0) {
        PPanic("Failed to create queue for outgoing Zeus connection");
    }

    this->receiver = src;
    int res;
    if ((res = Zeus::connect(qd,
                             (struct sockaddr *)&(dst.addr),
                             sizeof(dst.addr))) < 0) {
        Panic("Failed to connect %s:%d: %s",
              inet_ntoa(dst.addr.sin_addr),
              htons(dst.addr.sin_port),
              strerror(res));
        return;
    }

    // Tell the receiver its address
    struct sockaddr_in sin;
    socklen_t sinsize = sizeof(sin);
    if (getsockname(Zeus::qd2fd(qd), (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    ZeusTransportAddress *addr = new ZeusTransportAddress(sin);
    src->SetAddress(addr);

    zeusOutgoing.insert(make_pair(*addr, qd));
    zeusIncoming.insert(make_pair(qd, *addr));

    Debug("Opened Zeus connection to %s:%d",
	  inet_ntoa(dst.addr.sin_addr), htons(dst.addr.sin_port));
}

void
ZeusTransport::Register(TransportReceiver *receiver,
                       const transport::Configuration &config,
                       int replicaIdx)
{
    ASSERT(replicaIdx < config.n);
    struct sockaddr_in sin;

    //const transport::Configuration *canonicalConfig =
    RegisterConfiguration(receiver, config, replicaIdx);
    this->replicaIdx = replicaIdx;
    // Clients don't need to accept Zeus connections
    if (replicaIdx == -1) {
        return;
    }
    
    // Create socket
    int qd;
    if ((qd = Zeus::socket(AF_INET, SOCK_STREAM, 0)) < 0) {
        PPanic("Failed to create socket to accept Zeus connections");
    }

    // Registering a replica. Bind socket to the designated
    // host/port
    const string &host = config.replica(replicaIdx).host;
    const string &port = config.replica(replicaIdx).port;
    BindToPort(qd, host, port);
    
    // Listen for connections
    if (Zeus::listen(qd, 5) < 0) {
        PPanic("Failed to listen for Zeus connections");
    }
        
    // Create event to accept connections
    this->acceptQD = qd;
    this->receiver = receiver;    
    
    // Tell the receiver its address
    socklen_t sinsize = sizeof(sin);
    if (getsockname(Zeus::qd2fd(qd), (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    ZeusTransportAddress *addr = new ZeusTransportAddress(sin);
    receiver->SetAddress(addr);

    Debug("Accepting connections on Zeus port %hu", ntohs(sin.sin_port));
}

bool
ZeusTransport::SendMessageInternal(TransportReceiver *src,
                                  const ZeusTransportAddress &dst,
                                  const Message &m,
                                  bool multicast)
{
    auto it = zeusOutgoing.find(dst);
    // See if we have a connection open
    if (it == zeusOutgoing.end()) {
        ConnectZeus(src, dst);
        it = zeusOutgoing.find(dst);
    }

    if (it == zeusOutgoing.end()) {
        return false;
    }
    
    int qd = it->second;
    
    // Serialize message
    string data = m.SerializeAsString();
    string type = m.GetTypeName();
    size_t typeLen = type.length();
    size_t dataLen = data.length();
    size_t totalLen = (typeLen + sizeof(typeLen) +
                       dataLen + sizeof(dataLen) +
                       sizeof(totalLen) +
                       sizeof(uint32_t));

    char buf[totalLen];
    Zeus::sgarray sga;
    sga.num_bufs = 1;
    sga.bufs[0].buf = (Zeus::ioptr)&buf[0];
    sga.bufs[0].len = totalLen;
    char *ptr = &buf[0];

    *((uint32_t *) ptr) = MAGIC;
    ptr += sizeof(uint32_t);
    ASSERT((size_t)(ptr-buf) < totalLen);
    
    *((size_t *) ptr) = totalLen;
    ptr += sizeof(size_t);
    ASSERT((size_t)(ptr-buf) < totalLen);

    *((size_t *) ptr) = typeLen;
    ptr += sizeof(size_t);
    ASSERT((size_t)(ptr-buf) < totalLen);

    ASSERT((size_t)(ptr+typeLen-buf) < totalLen);
    memcpy(ptr, type.c_str(), typeLen);
    ptr += typeLen;
    *((size_t *) ptr) = dataLen;
    ptr += sizeof(size_t);

    ASSERT((size_t)(ptr-buf) < totalLen);
    ASSERT((size_t)(ptr+dataLen-buf) == totalLen);
    memcpy(ptr, data.c_str(), dataLen);
    ptr += dataLen;

    Zeus::qtoken t = Zeus::push(qd, sga);
    if (t != 0) {
        Debug("Waiting to send");
        ssize_t res = Zeus::wait(t, sga);
        if (res < 0 || (size_t)res < totalLen) {
            Warning("Failed to write to Zeus buffer");
            return false;
        }
    }

    Debug("Sent %ld byte %s message to server over Zeus",
          totalLen, type.c_str());
    return true;
}

void
ZeusTransport::Run()
{
    qtoken tokens[MAX_CONNECTIONS];
    memset(tokens, 0, sizeof(qtoken) * MAX_CONNECTIONS);
    int i = 0, offset;
    sgarray sga;
    qtoken qt = 0;
    ssize_t res;
    int qd;
           
    while (!stopLoop) {
        // check accept
        while (tokens[0] == 0) {
            qt = pop(acceptQD, sga);
            if (qt == 0) ZeusAcceptCallback();
            else tokens[0] = qt;
        }

        // check timer
        while (tokens[1] == 0) {
            qt = pop(timerQD, sga);
            if (qt == 0) OnTimer((ZeusTransportTimerInfo *)sga.bufs[0].buf);
            else tokens[1] = qt;
        }

        for (auto &it : receivers) {
            qd = it.first;
            while (tokens[i] == 0) {
                qt = pop(qd, sga);
                if (qt == 0) ZeusPopCallback(qd, receivers[qd], sga);
                else tokens[i] = qt;
            }
            i++;
        }

        
        // wait for any of the pops to return
        // i is now set to number of tokens
        // offset will return the token that is ready
        // qd will return qd of the queue that is ready
        res = wait_any(tokens, i, offset, qd, sga);
        assert(res > 0);
        // zero out the token for the next round
        tokens[offset] = 0;
        if (qd == acceptQD) ZeusAcceptCallback();
        else if (qd == timerQD)
            OnTimer((ZeusTransportTimerInfo *)sga.bufs[0].buf);
        else 
            ZeusPopCallback(qd, receivers[qd], sga);        
    }        
}

void
ZeusTransport::Stop()
{
    stopLoop = true;
}

int
ZeusTransport::Timer(uint64_t ms, timer_callback_t cb)
{
    ZeusTransportTimerInfo *info = new ZeusTransportTimerInfo();
    ASSERT(ms == 0);
    ++lastTimerId;
    
    info->id = lastTimerId;
    info->cb = cb;

    timers[info->id] = info;

    sgarray sga;
    sga.bufs[0].buf = info;
    sga.bufs[0].len = sizeof(ZeusTransportTimerInfo);
    ssize_t res = push(timerQD, sga);
    ASSERT(res == sga.bufs[0].len);
    
    return info->id;
}

bool
ZeusTransport::CancelTimer(int id)
{
    ZeusTransportTimerInfo *info = timers[id];

    if (info == NULL) {
        return false;
    }

    timers.erase(info->id);
    delete info;
    
    return true;
}

void
ZeusTransport::CancelAllTimers()
{
    while (!timers.empty()) {
        auto kv = timers.begin();
        CancelTimer(kv->first);
    }
}

void
ZeusTransport::OnTimer(ZeusTransportTimerInfo *info)
{
    timers.erase(info->id);
    info->cb();
    delete info;
}

static void
ZeusSignalCallback(int signal)
{
    ASSERT(signal == SIGTERM || signal == SIGINT);
    stopLoop = true;
}

void
ZeusTransport::ZeusAcceptCallback()
{
    int newqd;
    struct sockaddr_in sin;
    socklen_t sinLength = sizeof(sin);
        
    // Accept a connection
    if ((newqd = Zeus::accept(acceptQD,
                              (struct sockaddr *)&sin,
                              &sinLength)) < 0) {
        PWarning("Failed to accept incoming Zeus connection");
        return;
    }

    ZeusTransportAddress *client = new ZeusTransportAddress(sin);
    zeusOutgoing.insert(make_pair(*client, newqd));
    zeusIncoming.insert(make_pair(newqd, *client));
        
    Debug("Opened incoming Zeus connection from %s:%d",
          inet_ntoa(sin.sin_addr), htons(sin.sin_port));
}

void
    ZeusTransport::ZeusPopCallback(int qd,
                                   TransportReceiver *receiver,
                                   sgarray &sga)
                                   
{
    Debug("Pop Callback");
    auto addr = zeusIncoming.find(qd);
    
    ASSERT(sga.num_bufs == 1);
    uint8_t *ptr = (uint8_t *)sga.bufs[0].buf;
    ASSERT(sga.bufs[0].len > 0);
    uint32_t magic = *(uint32_t *)ptr;
    ptr += sizeof(magic);
    ASSERT(magic == MAGIC);
    size_t totalSize = *((size_t *)ptr);
    ptr += sizeof(totalSize);
    size_t typeLen = *((size_t *)ptr);
    ptr += sizeof(typeLen);
    string type((char *)ptr, typeLen);
    ptr += typeLen;
    size_t msgLen = *((size_t *)ptr);
    ptr += sizeof(msgLen);
    string data((char *)ptr, msgLen);;
    ptr += msgLen;
    
    // Dispatch
    receiver->ReceiveMessage(addr->second,
                             type,
                             data);
    free(sga.bufs[0].buf);
    Debug("Done processing large %s message", type.c_str());        
}
