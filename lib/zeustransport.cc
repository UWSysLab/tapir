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
#include <signal.h>

const size_t MAX_Zeus_SIZE = 100; // XXX
const uint32_t MAGIC = 0x06121983;

using std::pair;

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
        if ((res = getaddrinfo(addr.host.c_str(), addr.port.c_str(),
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
    
    // Set up libevent
    evthread_use_pthreads();
    event_set_log_callback(LogCallback);
    event_set_fatal_callback(FatalCallback);

    libeventBase = event_base_new();
    evthread_make_base_notifiable(libeventBase);

    // Set up signal handler
    if (handleSignals) {
        signalEvents.push_back(evsignal_new(libeventBase, SIGTERM,
                                            SignalCallback, this));
        signalEvents.push_back(evsignal_new(libeventBase, SIGINT,
                                            SignalCallback, this));
        for (event *x : signalEvents) {
            event_add(x, NULL);
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
    if ((qd = Zeus::queue(AF_INET, SOCK_STREAM, 0)) < 0) {
        PPanic("Failed to create queue for outgoing Zeus connection");
    }

    ZeusTransportZeusListener *info = new ZeusTransportZeusListener();
    info->transport = this;
    info->qd = qd;
    info->receiver = src;
    info->replicaIdx = -1;

    int res;
    if ((res = Zeus::connect(qd,
                             (struct sockaddr *)&(dst.addr),
                             sizeof(dst.addr))) < 0) {
        Panic("Failed to connect %s:%d: %s",
              inet_ntoa(dst.addr.sin_addr), htons(dst.addr.sin_port), strerror(res));
        return;
    }

    int fd = Zeus::qd2fd(qd);
    
    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK on outgoing Zeus socket");
    }

    // Set TCP_NODELAY
    int n = 1;
    if (setsockopt(fd, IPPROTO_TCP,
                   TCP_NODELAY, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set TCP_NODELAY on Zeus connecting socket");
    }

    // Create an libevent event for the completion channel
    info->ev = event_new(libeventBase,
                         fd,
                         EV_READ | EV_PERSIST,
                         &ZeusReadableCallback,
                         (void *)info);
    event_add(info->ev, NULL);

    
    // Tell the receiver its address
    struct sockaddr_in sin;
    socklen_t sinsize = sizeof(sin);
    if (getsockname(fd, (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    ZeusTransportAddress *addr = new ZeusTransportAddress(sin);
    src->SetAddress(addr);

    zeusOutgoing[dst] = qd;
    zeusIncoming[info] = dst.clone();

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

    // Clients don't need to accept Zeus connections
    if (replicaIdx == -1) {
        return;
    }
    
    // Create socket
    int qd;
    if ((qd = Zeus::queue(AF_INET, SOCK_STREAM, 0)) < 0) {
        PPanic("Failed to create socket to accept Zeus connections");
    }

    int fd = Zeus::qd2fd(qd);
    
    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Set SO_REUSEADDR
    int n;
    if (setsockopt(fd, SOL_SOCKET,
                   SO_REUSEADDR, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_REUSEADDR on Zeus listening socket");
    }

    // Set TCP_NODELAY
    n = 1;
    if (setsockopt(fd, IPPROTO_TCP,
                   TCP_NODELAY, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set TCP_NODELAY on Zeus listening socket");
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
    ZeusTransportZeusListener *info = new ZeusTransportZeusListener();
    info->transport = this;
    info->qd = qd;
    info->receiver = receiver;
    info->replicaIdx = replicaIdx;
    info->ev = event_new(libeventBase, fd,
                         EV_READ | EV_PERSIST,
                         &ZeusAcceptCallback, (void *)info);
    event_add(info->ev, NULL);
    
    // Tell the receiver its address
    socklen_t sinsize = sizeof(sin);
    if (getsockname(fd, (sockaddr *) &sin, &sinsize) < 0) {
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
    auto kv = zeusOutgoing.find(dst);
    // See if we have a connection open
    if (kv == zeusOutgoing.end()) {
        ConnectZeus(src, dst);
        kv = zeusOutgoing.find(dst);
    }

    if (kv == zeusOutgoing.end()) {
        return false;
    }
    
    int qd = kv->second;
    
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

    ssize_t res = Zeus::push(qd, sga);
    if (res < 0 || (size_t)res < totalLen) {
        Warning("Failed to write to Zeus buffer");
        return false;
    }

    Debug("Sent %ld byte %s message to server over Zeus",
          totalLen, type.c_str());
    return true;
}

void
ZeusTransport::Run()
{
    event_base_dispatch(libeventBase);
}

void
ZeusTransport::Stop()
{
    event_base_loopbreak(libeventBase);
}

int
ZeusTransport::Timer(uint64_t ms, timer_callback_t cb)
{
    std::lock_guard<std::mutex> lck(mtx);
    
    ZeusTransportTimerInfo *info = new ZeusTransportTimerInfo();

    struct timeval tv;
    tv.tv_sec = ms/1000;
    tv.tv_usec = (ms % 1000) * 1000;
    
    ++lastTimerId;
    
    info->transport = this;
    info->id = lastTimerId;
    info->cb = cb;
    info->ev = event_new(libeventBase, -1, 0,
                         TimerCallback, info);

    timers[info->id] = info;
    
    event_add(info->ev, &tv);
    
    return info->id;
}

bool
ZeusTransport::CancelTimer(int id)
{
    std::lock_guard<std::mutex> lck(mtx);
    ZeusTransportTimerInfo *info = timers[id];

    if (info == NULL) {
        return false;
    }

    timers.erase(info->id);
    event_del(info->ev);
    event_free(info->ev);
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
    {
	    std::lock_guard<std::mutex> lck(mtx);
	    
	    timers.erase(info->id);
	    event_del(info->ev);
	    event_free(info->ev);
    }
    
    info->cb();

    delete info;
}

void
ZeusTransport::TimerCallback(evutil_socket_t fd, short what, void *arg)
{
    ZeusTransport::ZeusTransportTimerInfo *info =
        (ZeusTransport::ZeusTransportTimerInfo *)arg;

    ASSERT(what & EV_TIMEOUT);

    info->transport->OnTimer(info);
}

void
ZeusTransport::LogCallback(int severity, const char *msg)
{
    Message_Type msgType;
    switch (severity) {
    case _EVENT_LOG_DEBUG:
        msgType = MSG_DEBUG;
        break;
    case _EVENT_LOG_MSG:
        msgType = MSG_NOTICE;
        break;
    case _EVENT_LOG_WARN:
        msgType = MSG_WARNING;
        break;
    case _EVENT_LOG_ERR:
        msgType = MSG_WARNING;
        break;
    default:
        NOT_REACHABLE();
    }

    _Message(msgType, "libevent", 0, NULL, "%s", msg);
}

void
ZeusTransport::FatalCallback(int err)
{
    Panic("Fatal libevent error: %d", err);
}

void
ZeusTransport::SignalCallback(evutil_socket_t fd, short what, void *arg)
{
    Debug("Terminating on SIGTERM/SIGINT");
    ZeusTransport *transport = (ZeusTransport *)arg;
    event_base_loopbreak(transport->libeventBase);
}

void
ZeusTransport::ZeusAcceptCallback(evutil_socket_t fd, short what, void *arg)
{
    ZeusTransportZeusListener *info = (ZeusTransportZeusListener *)arg;
    ZeusTransport *transport = info->transport;
    
    if (what & EV_READ) {
        int newqd;
        struct sockaddr_in sin;
        socklen_t sinLength = sizeof(sin);
        
        // Accept a connection
        if ((newqd = Zeus::accept(info->qd,
                                  (struct sockaddr *)&sin,
                                  &sinLength)) < 0) {
            PWarning("Failed to accept incoming Zeus connection");
            return;
        }

        ZeusTransportZeusListener *newinfo = new ZeusTransportZeusListener();
        newinfo->transport = transport;
        newinfo->receiver = info->receiver;
        newinfo->qd = newqd;
        
        int newfd = Zeus::qd2fd(newqd);
        // Put it in non-blocking mode
        if (fcntl(newfd, F_SETFL, O_NONBLOCK, 1)) {
            PWarning("Failed to set O_NONBLOCK");
        }

        // Set TCP_NODELAY
        int n = 1;
        if (setsockopt(fd, IPPROTO_TCP,
                       TCP_NODELAY, (char *)&n, sizeof(n)) < 0) {
            PWarning("Failed to set TCP_NODELAY on Zeus connecting socket");
        }

        // Create an libevent event for the completion channel
        newinfo->ev = event_new(transport->libeventBase,
                                newfd,
                                EV_READ | EV_PERSIST,
                                &ZeusReadableCallback,
                                (void *)newinfo);
        event_add(newinfo->ev, NULL);

        ZeusTransportAddress client = ZeusTransportAddress(sin);
        transport->zeusOutgoing[client] = newqd;
        transport->zeusIncoming[newinfo] = client.clone();
        
        Debug("Opened incoming Zeus connection from %s:%d",
               inet_ntoa(sin.sin_addr), htons(sin.sin_port));
    } 
}

void
ZeusTransport::ZeusReadableCallback(evutil_socket_t fd, short what, void *arg)
{

    Debug("Readable Callback");
    ZeusTransportZeusListener *info = (ZeusTransportZeusListener *)arg;
    ZeusTransport *transport = info->transport;
    auto addr = transport->zeusIncoming.find(info);
    struct Zeus::sgarray sga;
    
    while (Zeus::pop(info->qd, sga) > 0) {
        ASSERT(sga.num_bufs == 1);

        uint8_t *ptr = (uint8_t *)sga.bufs[0].buf;
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
        info->receiver->ReceiveMessage(*addr->second,
                                       type,
                                       data);
        Debug("Done processing large %s message", type.c_str());
        free(sga.bufs[0].buf);
    }
}
