// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * tcptransport.cc:
 *   message-passing network interface that uses TCP message delivery
 *   and libasync
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

#include "lib/assert.h"
#include "lib/configuration.h"
#include "lib/message.h"
#include "lib/tcptransport.h"

#include <google/protobuf/message.h>
#include <event2/thread.h>

#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <signal.h>

const size_t MAX_TCP_SIZE = 100; // XXX
const uint32_t MAGIC = 0x06121983;

using std::pair;

TCPTransportAddress::TCPTransportAddress(const sockaddr_in &addr)
    : addr(addr)
{
    memset((void *)addr.sin_zero, 0, sizeof(addr.sin_zero));
}

TCPTransportAddress *
TCPTransportAddress::clone() const
{
    TCPTransportAddress *c = new TCPTransportAddress(*this);
    return c;    
}

bool operator==(const TCPTransportAddress &a, const TCPTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) == 0);
}

bool operator!=(const TCPTransportAddress &a, const TCPTransportAddress &b)
{
    return !(a == b);
}

bool operator<(const TCPTransportAddress &a, const TCPTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) < 0);
}

TCPTransportAddress
TCPTransport::LookupAddress(const transport::ReplicaAddress &addr)
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
        TCPTransportAddress out =
            TCPTransportAddress(*((sockaddr_in *)ai->ai_addr));
        freeaddrinfo(ai);
        return out;
}

TCPTransportAddress
TCPTransport::LookupAddress(const transport::Configuration &config,
                            int idx)
{
    const transport::ReplicaAddress &addr = config.replica(idx);
    return LookupAddress(addr);
}

static void
BindToPort(int fd, const string &host, const string &port)
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

    Debug("Binding to %s %d TCP", inet_ntoa(sin.sin_addr), htons(sin.sin_port));

    if (bind(fd, (sockaddr *)&sin, sizeof(sin)) < 0) {
        PPanic("Failed to bind to socket");
    }
}

TCPTransport::TCPTransport(double dropRate, double reorderRate,
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
}

TCPTransport::~TCPTransport()
{
    // XXX Shut down libevent?

    // for (auto kv : timers) {
    //     delete kv.second;
    // }
}

void
TCPTransport::ConnectTCP(TransportReceiver *src, const TCPTransportAddress &dst)
{
    // Create socket
    int fd;
    if ((fd = socket(AF_INET, SOCK_STREAM, 0)) < 0) {
        PPanic("Failed to create socket for outgoing TCP connection");
    }
    
    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK on outgoing TCP socket");
    }

    // Set TCP_NODELAY
    int n = 1;
    if (setsockopt(fd, IPPROTO_TCP,
                   TCP_NODELAY, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set TCP_NODELAY on TCP listening socket");
    }

    TCPTransportTCPListener *info = new TCPTransportTCPListener();
    info->transport = this;
    info->acceptFd = 0;
    info->receiver = src;
    info->replicaIdx = -1;
    info->acceptEvent = NULL;
    
    tcpListeners.push_back(info);

    struct bufferevent *bev =
        bufferevent_socket_new(libeventBase, fd,
                               BEV_OPT_CLOSE_ON_FREE);
    bufferevent_setcb(bev, TCPReadableCallback, NULL,
                      TCPOutgoingEventCallback, info);
    
    if (bufferevent_socket_connect(bev,
                                   (struct sockaddr *)&(dst.addr),
                                   sizeof(dst.addr)) < 0) {
	bufferevent_free(bev);
        Warning("Failed to connect to server via TCP");
        return;
    }
    if (bufferevent_enable(bev, EV_READ|EV_WRITE) < 0) {
        Panic("Failed to enable bufferevent");
    }

    // Tell the receiver its address
    struct sockaddr_in sin;
    socklen_t sinsize = sizeof(sin);
    if (getsockname(fd, (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    TCPTransportAddress *addr = new TCPTransportAddress(sin);
    src->SetAddress(addr);

    tcpOutgoing[dst] = bev;
    tcpAddresses.insert(pair<struct bufferevent*, TCPTransportAddress>(bev,dst));

    Debug("Opened TCP connection to %s:%d",
	  inet_ntoa(dst.addr.sin_addr), htons(dst.addr.sin_port));
}

void
TCPTransport::Register(TransportReceiver *receiver,
                       const transport::Configuration &config,
                       int replicaIdx)
{
    ASSERT(replicaIdx < config.n);
    struct sockaddr_in sin;

    //const transport::Configuration *canonicalConfig =
    RegisterConfiguration(receiver, config, replicaIdx);

    // Clients don't need to accept TCP connections
    if (replicaIdx == -1) {
	return;
    }
    
    // Create socket
    int fd;
    if ((fd = socket(AF_INET, SOCK_STREAM, 0)) < 0) {
        PPanic("Failed to create socket to accept TCP connections");
    }

    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Set SO_REUSEADDR
    int n;
    if (setsockopt(fd, SOL_SOCKET,
                   SO_REUSEADDR, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_REUSEADDR on TCP listening socket");
    }

    // Set TCP_NODELAY
    n = 1;
    if (setsockopt(fd, IPPROTO_TCP,
                   TCP_NODELAY, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set TCP_NODELAY on TCP listening socket");
    }

    // Registering a replica. Bind socket to the designated
    // host/port
    const string &host = config.replica(replicaIdx).host;
    const string &port = config.replica(replicaIdx).port;
    BindToPort(fd, host, port);
    
    // Listen for connections
    if (listen(fd, 5) < 0) {
        PPanic("Failed to listen for TCP connections");
    }
        
    // Create event to accept connections
    TCPTransportTCPListener *info = new TCPTransportTCPListener();
    info->transport = this;
    info->acceptFd = fd;
    info->receiver = receiver;
    info->replicaIdx = replicaIdx;
    info->acceptEvent = event_new(libeventBase, fd,
                                  EV_READ | EV_PERSIST,
                                  TCPAcceptCallback, (void *)info);
    event_add(info->acceptEvent, NULL);
    tcpListeners.push_back(info);

    // Tell the receiver its address
    socklen_t sinsize = sizeof(sin);
    if (getsockname(fd, (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    TCPTransportAddress *addr = new TCPTransportAddress(sin);
    receiver->SetAddress(addr);

    // Update mappings
    receivers[fd] = receiver;
    fds[receiver] = fd;

    Debug("Accepting connections on TCP port %hu", ntohs(sin.sin_port));
}

bool
TCPTransport::SendMessageInternal(TransportReceiver *src,
                                  const TCPTransportAddress &dst,
                                  const Message &m,
                                  bool multicast)
{
    auto kv = tcpOutgoing.find(dst);
    // See if we have a connection open
    if (kv == tcpOutgoing.end()) {
        ConnectTCP(src, dst);
        kv = tcpOutgoing.find(dst);
    }
    
    struct bufferevent *ev = kv->second;
    ASSERT(ev != NULL);

    // Serialize message
    string data = m.SerializeAsString();
    string type = m.GetTypeName();
    size_t typeLen = type.length();
    size_t dataLen = data.length();
    size_t totalLen = (typeLen + sizeof(typeLen) +
                       dataLen + sizeof(dataLen) +
                       sizeof(totalLen) +
                       sizeof(uint32_t));

    Debug("Sending %ld byte %s message to server over TCP",
          totalLen, type.c_str());
    
    char buf[totalLen];
    char *ptr = buf;

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

    if (bufferevent_write(ev, buf, totalLen) < 0) {
        Warning("Failed to write to TCP buffer");
        return false;
    }
    
    return true;
}

void
TCPTransport::Run()
{
    event_base_dispatch(libeventBase);
}

void
TCPTransport::Stop()
{
    event_base_loopbreak(libeventBase);
}

int
TCPTransport::Timer(uint64_t ms, timer_callback_t cb)
{
    std::lock_guard<std::mutex> lck(mtx);
    
    TCPTransportTimerInfo *info = new TCPTransportTimerInfo();

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
TCPTransport::CancelTimer(int id)
{
    std::lock_guard<std::mutex> lck(mtx);
    TCPTransportTimerInfo *info = timers[id];

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
TCPTransport::CancelAllTimers()
{
    while (!timers.empty()) {
        auto kv = timers.begin();
        CancelTimer(kv->first);
    }
}

void
TCPTransport::OnTimer(TCPTransportTimerInfo *info)
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
TCPTransport::TimerCallback(evutil_socket_t fd, short what, void *arg)
{
    TCPTransport::TCPTransportTimerInfo *info =
        (TCPTransport::TCPTransportTimerInfo *)arg;

    ASSERT(what & EV_TIMEOUT);

    info->transport->OnTimer(info);
}

void
TCPTransport::LogCallback(int severity, const char *msg)
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
TCPTransport::FatalCallback(int err)
{
    Panic("Fatal libevent error: %d", err);
}

void
TCPTransport::SignalCallback(evutil_socket_t fd, short what, void *arg)
{
    Debug("Terminating on SIGTERM/SIGINT");
    TCPTransport *transport = (TCPTransport *)arg;
    event_base_loopbreak(transport->libeventBase);
}

void
TCPTransport::TCPAcceptCallback(evutil_socket_t fd, short what, void *arg)
{
    TCPTransportTCPListener *info = (TCPTransportTCPListener *)arg;
    TCPTransport *transport = info->transport;
    
    if (what & EV_READ) {
        int newfd;
        struct sockaddr_in sin;
        socklen_t sinLength = sizeof(sin);
        struct bufferevent *bev;

        // Accept a connection
        if ((newfd = accept(fd, (struct sockaddr *)&sin,
                            &sinLength)) < 0) {
            PWarning("Failed to accept incoming TCP connection");
            return;
        }

        // Put it in non-blocking mode
        if (fcntl(newfd, F_SETFL, O_NONBLOCK, 1)) {
            PWarning("Failed to set O_NONBLOCK");
        }

            // Set TCP_NODELAY
        int n = 1;
        if (setsockopt(newfd, IPPROTO_TCP,
                       TCP_NODELAY, (char *)&n, sizeof(n)) < 0) {
            PWarning("Failed to set TCP_NODELAY on TCP listening socket");
        }

        // Create a buffered event
        bev = bufferevent_socket_new(transport->libeventBase, newfd,
                                     BEV_OPT_CLOSE_ON_FREE);
        bufferevent_setcb(bev, TCPReadableCallback, NULL,
                          TCPIncomingEventCallback, info);
        if (bufferevent_enable(bev, EV_READ|EV_WRITE) < 0) {
            Panic("Failed to enable bufferevent");
        }

        info->connectionEvents.push_back(bev);
	TCPTransportAddress client = TCPTransportAddress(sin);
	transport->tcpOutgoing[client] = bev;
	transport->tcpAddresses.insert(pair<struct bufferevent*, TCPTransportAddress>(bev,client));
        Debug("Opened incoming TCP connection from %s:%d",
               inet_ntoa(sin.sin_addr), htons(sin.sin_port));
    } 
}

void
TCPTransport::TCPReadableCallback(struct bufferevent *bev, void *arg)
{
    TCPTransportTCPListener *info = (TCPTransportTCPListener *)arg;
    TCPTransport *transport = info->transport;
    struct evbuffer *evbuf = bufferevent_get_input(bev);

    Debug("Readable on bufferevent %p", bev);
    

    while (evbuffer_get_length(evbuf) > 0) {
        uint32_t *magic;
        magic = (uint32_t *)evbuffer_pullup(evbuf, sizeof(*magic));
        if (magic == NULL) {
            return;
        }
        ASSERT(*magic == MAGIC);
    
        size_t *sz;
        unsigned char *x = evbuffer_pullup(evbuf, sizeof(*magic) + sizeof(*sz));
        
        sz = (size_t *) (x + sizeof(*magic));
        if (x == NULL) {
            return;
        }
        size_t totalSize = *sz;
        ASSERT(totalSize < 1073741826);
        
        if (evbuffer_get_length(evbuf) < totalSize) {
            Debug("Don't have %ld bytes for a message yet, only %ld",
                  totalSize, evbuffer_get_length(evbuf));
            return;
        }
        Debug("Receiving %ld byte message", totalSize);
        
        char buf[totalSize];
        size_t copied = evbuffer_remove(evbuf, buf, totalSize);
        ASSERT(copied == totalSize);
        
        // Parse message
        char *ptr = buf + sizeof(*sz) + sizeof(*magic);
        
        size_t typeLen = *((size_t *)ptr);
        ptr += sizeof(size_t);
        ASSERT((size_t)(ptr-buf) < totalSize);
        
        ASSERT((size_t)(ptr+typeLen-buf) < totalSize);
        string msgType(ptr, typeLen);
        ptr += typeLen;
        
        size_t msgLen = *((size_t *)ptr);
        ptr += sizeof(size_t);
        ASSERT((size_t)(ptr-buf) < totalSize);
        
        ASSERT((size_t)(ptr+msgLen-buf) <= totalSize);
        string msg(ptr, msgLen);
        ptr += msgLen;
        
        auto addr = transport->tcpAddresses.find(bev);
        ASSERT(addr != transport->tcpAddresses.end());
        
        // Dispatch
        info->receiver->ReceiveMessage(addr->second, msgType, msg);
        Debug("Done processing large %s message", msgType.c_str());
    }
}

void
TCPTransport::TCPIncomingEventCallback(struct bufferevent *bev,
                                       short what, void *arg)
{
    if (what & BEV_EVENT_ERROR) {
        Warning("Error on incoming TCP connection: %s",
                evutil_socket_error_to_string(EVUTIL_SOCKET_ERROR()));
        bufferevent_free(bev);
        return;
    } else if (what & BEV_EVENT_ERROR) {
        Warning("EOF on incoming TCP connection");
        bufferevent_free(bev);
        return;
    }
}

void
TCPTransport::TCPOutgoingEventCallback(struct bufferevent *bev,
                                       short what, void *arg)
{
    TCPTransportTCPListener *info = (TCPTransportTCPListener *)arg;
    TCPTransport *transport = info->transport;
    auto it = transport->tcpAddresses.find(bev);    
    ASSERT(it != transport->tcpAddresses.end());
    TCPTransportAddress addr = it->second;
    
    if (what & BEV_EVENT_CONNECTED) {
        Debug("Established outgoing TCP connection to server");
    } else if (what & BEV_EVENT_ERROR) {
        Warning("Error on outgoing TCP connection to server: %s",
                evutil_socket_error_to_string(EVUTIL_SOCKET_ERROR()));
        bufferevent_free(bev);
        auto it2 = transport->tcpOutgoing.find(addr);
        transport->tcpOutgoing.erase(it2);
        transport->tcpAddresses.erase(bev);
        return;
    } else if (what & BEV_EVENT_EOF) {
        Warning("EOF on outgoing TCP connection to server");
        bufferevent_free(bev);
        auto it2 = transport->tcpOutgoing.find(addr);
        transport->tcpOutgoing.erase(it2);
        transport->tcpAddresses.erase(bev);
        return;
    }
}
