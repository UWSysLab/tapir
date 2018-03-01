// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * udptransport.cc:
 *   message-passing network interface that uses UDP message delivery
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
#include "lib/udptransport.h"

#include <google/protobuf/message.h>
#include <event2/event.h>
#include <event2/thread.h>

#include <memory>
#include <random>

#include <arpa/inet.h>
#include <netinet/in.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <signal.h>

const size_t MAX_UDP_MESSAGE_SIZE = 9000; // XXX
const int SOCKET_BUF_SIZE = 10485760;

using std::pair;

UDPTransportAddress::UDPTransportAddress(const sockaddr_in &addr)
    : addr(addr)
{
    memset((void *)addr.sin_zero, 0, sizeof(addr.sin_zero));
}

UDPTransportAddress *
UDPTransportAddress::clone() const
{
    UDPTransportAddress *c = new UDPTransportAddress(*this);
    return c;    
}

bool operator==(const UDPTransportAddress &a, const UDPTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) == 0);
}

bool operator!=(const UDPTransportAddress &a, const UDPTransportAddress &b)
{
    return !(a == b);
}

bool operator<(const UDPTransportAddress &a, const UDPTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) < 0);
}

UDPTransportAddress
UDPTransport::LookupAddress(const transport::ReplicaAddress &addr)
{
    int res;
    struct addrinfo hints;
    hints.ai_family   = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;
    hints.ai_protocol = 0;
    hints.ai_flags    = 0;
    struct addrinfo *ai;
    if ((res = getaddrinfo(addr.host.c_str(), addr.port.c_str(), &hints, &ai))) {
        Panic("Failed to resolve %s:%s: %s",
              addr.host.c_str(), addr.port.c_str(), gai_strerror(res));
    }
    if (ai->ai_addr->sa_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");
    }
    UDPTransportAddress out =
              UDPTransportAddress(*((sockaddr_in *)ai->ai_addr));
    freeaddrinfo(ai);
    return out;
}

UDPTransportAddress
UDPTransport::LookupAddress(const transport::Configuration &config,
                            int idx)
{
    const transport::ReplicaAddress &addr = config.replica(idx);
    return LookupAddress(addr);
}

const UDPTransportAddress *
UDPTransport::LookupMulticastAddress(const transport::Configuration
                                     *config)
{
    if (!config->multicast()) {
        // Configuration has no multicast address
        return NULL;
    }

    if (multicastFds.find(config) != multicastFds.end()) {
        // We are listening on this multicast address. Some
        // implementations of MOM aren't OK with us both sending to
        // and receiving from the same address, so don't look up the
        // address.
        return NULL;
    }

    UDPTransportAddress *addr =
        new UDPTransportAddress(LookupAddress(*(config->multicast())));
    return addr;
}

static void
BindToPort(int fd, const string &host, const string &port)
{
    struct sockaddr_in sin;

    if ((host == "") && (port == "any")) {
        // Set up the sockaddr so we're OK with any UDP socket
        memset(&sin, 0, sizeof(sin));
        sin.sin_family = AF_INET;
        sin.sin_port = 0;        
    } else {
        // Otherwise, look up its hostname and port number (which
        // might be a service name)
        struct addrinfo hints;
        hints.ai_family   = AF_INET;
        hints.ai_socktype = SOCK_DGRAM;
        hints.ai_protocol = 0;
        hints.ai_flags    = AI_PASSIVE;
        struct addrinfo *ai;
        int res;
        if ((res = getaddrinfo(host.c_str(), port.c_str(),
                               &hints, &ai))) {
            Panic("Failed to resolve host/port %s:%s: %s",
                  host.c_str(), port.c_str(), gai_strerror(res));
        }
        ASSERT(ai->ai_family == AF_INET);
        ASSERT(ai->ai_socktype == SOCK_DGRAM);
        if (ai->ai_addr->sa_family != AF_INET) {
            Panic("getaddrinfo returned a non IPv4 address");        
        }
        sin = *(sockaddr_in *)ai->ai_addr;
        
        freeaddrinfo(ai);
    }

    Debug("Binding to %s:%d", inet_ntoa(sin.sin_addr), htons(sin.sin_port));

    if (bind(fd, (sockaddr *)&sin, sizeof(sin)) < 0) {
        PPanic("Failed to bind to socket");
    }
}

UDPTransport::UDPTransport(double dropRate, double reorderRate,
        int dscp, bool handleSignals)
    : dropRate(dropRate), reorderRate(reorderRate), dscp(dscp)
{

    lastTimerId = 0;
    lastFragMsgId = 0;

    uniformDist = std::uniform_real_distribution<double>(0.0,1.0);
    randomEngine.seed(time(NULL));
    reorderBuffer.valid = false;
    if (dropRate > 0) {
        Warning("Dropping packets with probability %g", dropRate);
    }
    if (reorderRate > 0) {
        Warning("Reordering packets with probability %g", reorderRate);
    }
    
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

UDPTransport::~UDPTransport()
{
    // event_base_loopbreak(libeventBase);

    // for (auto kv : timers) {
    //     delete kv.second;
    // }

}

void
UDPTransport::ListenOnMulticastPort(const transport::Configuration
                                    *canonicalConfig)
{
    if (!canonicalConfig->multicast()) {
        // No multicast address specified
        return;
    }

    if (multicastFds.find(canonicalConfig) != multicastFds.end()) {
        // We're already listening
        return;    
    }

    int fd;
    
    // Create socket
    if ((fd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) {
        PPanic("Failed to create socket to listen for multicast");
    }
    
    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK on multicast socket");
    }
    
    int n = 1;
    if (setsockopt(fd, SOL_SOCKET,
                   SO_REUSEADDR, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_REUSEADDR on multicast socket");
    }

    // Increase buffer size
    n = SOCKET_BUF_SIZE;
    if (setsockopt(fd, SOL_SOCKET,
                   SO_RCVBUF, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_RCVBUF on socket");
    }
    if (setsockopt(fd, SOL_SOCKET,
                   SO_SNDBUF, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_SNDBUF on socket");
    }

    
    // Bind to the specified address
    BindToPort(fd,
               canonicalConfig->multicast()->host,
               canonicalConfig->multicast()->port);
    
    // Set up a libevent callback
    event *ev = event_new(libeventBase, fd,
                          EV_READ | EV_PERSIST,
                          SocketCallback, (void *)this);
    event_add(ev, NULL);
    listenerEvents.push_back(ev);

    // Record the fd
    multicastFds[canonicalConfig] = fd;
    multicastConfigs[fd] = canonicalConfig;

    Notice("Listening for multicast requests on %s:%s",
           canonicalConfig->multicast()->host.c_str(),
           canonicalConfig->multicast()->port.c_str());
}

void
UDPTransport::Register(TransportReceiver *receiver,
                       const transport::Configuration &config,
                       int replicaIdx)
{
    ASSERT(replicaIdx < config.n);
    struct sockaddr_in sin;

    const transport::Configuration *canonicalConfig =
        RegisterConfiguration(receiver, config, replicaIdx);

    // Create socket
    int fd;
    if ((fd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) {
        PPanic("Failed to create socket to listen");
    }

    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Enable outgoing broadcast traffic
    int n = 1;
    if (setsockopt(fd, SOL_SOCKET,
                   SO_BROADCAST, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_BROADCAST on socket");
    }

    if (dscp != 0) {
        n = dscp << 2;
        if (setsockopt(fd, IPPROTO_IP,
                       IP_TOS, (char *)&n, sizeof(n)) < 0) {
            PWarning("Failed to set DSCP on socket");
        }
    }
    
    // Increase buffer size
    n = SOCKET_BUF_SIZE;
    if (setsockopt(fd, SOL_SOCKET,
                   SO_RCVBUF, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_RCVBUF on socket");
    }
    if (setsockopt(fd, SOL_SOCKET,
                   SO_SNDBUF, (char *)&n, sizeof(n)) < 0) {
        PWarning("Failed to set SO_SNDBUF on socket");
    }
    
    if (replicaIdx != -1) {
        // Registering a replica. Bind socket to the designated
        // host/port
        const string &host = config.replica(replicaIdx).host;
        const string &port = config.replica(replicaIdx).port;
        BindToPort(fd, host, port);
    } else {
        // Registering a client. Bind to any available host/port
        BindToPort(fd, "", "any");        
    }

    // Set up a libevent callback
    event *ev = event_new(libeventBase, fd, EV_READ | EV_PERSIST,
                          SocketCallback, (void *)this);
    event_add(ev, NULL);
    listenerEvents.push_back(ev);

    // Tell the receiver its address
    socklen_t sinsize = sizeof(sin);
    if (getsockname(fd, (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    UDPTransportAddress *addr = new UDPTransportAddress(sin);
    receiver->SetAddress(addr);

    // Update mappings
    receivers[fd] = receiver;
    fds[receiver] = fd;

    Debug("Listening on UDP port %hu", ntohs(sin.sin_port));

    // If we are registering a replica, check whether we need to set
    // up a socket to listen on the multicast port.
    //
    // Don't do this if we're registering a client.
    if (replicaIdx != -1) {
        ListenOnMulticastPort(canonicalConfig);
    }
}

static size_t
SerializeMessage(const ::google::protobuf::Message &m,
                 std::unique_ptr<char[]> *out)
{
    string data = m.SerializeAsString();
    string type = m.GetTypeName();
    size_t typeLen = type.length();
    size_t dataLen = data.length();
    ssize_t totalLen = (typeLen + sizeof(typeLen) +
                       dataLen + sizeof(dataLen));

    std::unique_ptr<char[]> unique_buf(new char[totalLen]);
    char *buf = unique_buf.get();

    char *ptr = buf;
    *((size_t *) ptr) = typeLen;
    ptr += sizeof(size_t);
    ASSERT(ptr-buf < totalLen);
    ASSERT(ptr+typeLen-buf < totalLen);
    memcpy(ptr, type.c_str(), typeLen);
    ptr += typeLen;
    *((size_t *) ptr) = dataLen;
    ptr += sizeof(size_t);
    ASSERT(ptr-buf < totalLen);
    ASSERT(ptr+dataLen-buf == totalLen);
    memcpy(ptr, data.c_str(), dataLen);
    ptr += dataLen;

    *out = std::move(unique_buf);
    return totalLen;
}

bool
UDPTransport::SendMessageInternal(TransportReceiver *src,
                                  const UDPTransportAddress &dst,
                                  const Message &m,
                                  bool multicast)
{
    sockaddr_in sin = dynamic_cast<const UDPTransportAddress &>(dst).addr;

    // Serialize message
    std::unique_ptr<char[]> unique_buf;
    size_t msgLen = SerializeMessage(m, &unique_buf);
    char *buf = unique_buf.get();

    int fd = fds[src];

    // XXX All of this assumes that the socket is going to be
    // available for writing, which since it's a UDP socket it ought
    // to be.
    if (msgLen <= MAX_UDP_MESSAGE_SIZE) {
        if (sendto(fd, buf, msgLen, 0,
                   (sockaddr *)&sin, sizeof(sin)) < 0) {
            PWarning("Failed to send message");
            return false;
        }
    } else {
        int numFrags = ((msgLen-1) / MAX_UDP_MESSAGE_SIZE) + 1;
        Notice("Sending large %s message in %d fragments",
               m.GetTypeName().c_str(), numFrags);
        uint64_t msgId = ++lastFragMsgId;
        for (size_t fragStart = 0; fragStart < msgLen;
             fragStart += MAX_UDP_MESSAGE_SIZE) {
            size_t fragLen = std::min(msgLen - fragStart,
                                      MAX_UDP_MESSAGE_SIZE);
            size_t fragHeaderLen = 3*sizeof(size_t) + sizeof(uint64_t);
            char fragBuf[fragLen + fragHeaderLen];
            char *ptr = fragBuf;
            *((size_t *)ptr) = 0;
            ptr += sizeof(size_t);
            *((uint64_t *)ptr) = msgId;
            ptr += sizeof(uint64_t);
            *((size_t *)ptr) = fragStart;
            ptr += sizeof(size_t);
            *((size_t *)ptr) = msgLen;
            ptr += sizeof(size_t);
            memcpy(ptr, &buf[fragStart], fragLen);

            if (sendto(fd, fragBuf, fragLen + fragHeaderLen, 0,
                       (sockaddr *)&sin, sizeof(sin)) < 0) {
                PWarning("Failed to send message fragment %ld",
                         fragStart);
                return false;
            }
        }
    }

    return true;
}

void
UDPTransport::Run()
{
    event_base_dispatch(libeventBase);
}

void
UDPTransport::Stop()
{
    event_base_loopbreak(libeventBase);
}

static void
DecodePacket(const char *buf, size_t sz, string &type, string &msg)
{
    const char *ptr = buf;
    size_t typeLen = *((size_t *)ptr);
    ptr += sizeof(size_t);

    ASSERT(ptr-buf < (int)sz);
    ASSERT(ptr+typeLen-buf < (int)sz);

    type = string(ptr, typeLen);
    ptr += typeLen;

    size_t msgLen = *((size_t *)ptr);
    ptr += sizeof(size_t);

    ASSERT(ptr-buf < (int)sz);
    ASSERT(ptr+msgLen-buf <= (int)sz);

    msg = string(ptr, msgLen);
    ptr += msgLen;
    
}

void
UDPTransport::OnReadable(int fd)
{
    const int BUFSIZE = 65536;
    
    while (1) {
        ssize_t sz;
        char buf[BUFSIZE];
        sockaddr_in sender;
        socklen_t senderSize = sizeof(sender);
        
        sz = recvfrom(fd, buf, BUFSIZE, 0,
                      (struct sockaddr *) &sender, &senderSize);
        if (sz == -1) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                break;
            } else {
                PWarning("Failed to receive message from socket");
            }
        }
        
        UDPTransportAddress senderAddr(sender);
        string msgType, msg;

        // Take a peek at the first field. If it's all zeros, this is
        // a fragment. Otherwise, we can decode it directly.
        ASSERT(sizeof(size_t) - sz > 0);
        size_t typeLen = *((size_t *)buf);
        if (typeLen != 0) {
            // Not a fragment. Decode the packet
            DecodePacket(buf, sz, msgType, msg);
        } else {
            // This is a fragment. Decode the header
            const char *ptr = buf;
            ptr += sizeof(size_t);
            ASSERT(ptr-buf < sz);
            uint64_t msgId = *((uint64_t *)ptr);
            ptr += sizeof(uint64_t);
            ASSERT(ptr-buf < sz);
            size_t fragStart = *((size_t *)ptr);
            ptr += sizeof(size_t);
            ASSERT(ptr-buf < sz);
            size_t msgLen = *((size_t *)ptr);
            ptr += sizeof(size_t);
            ASSERT(ptr-buf < sz);
            ASSERT(buf+sz-ptr == (ssize_t) std::min(msgLen-fragStart,
                                                    MAX_UDP_MESSAGE_SIZE));
            Debug("Received fragment of %zd byte packet %lx starting at %zd",
                   msgLen, msgId, fragStart);
            UDPTransportFragInfo &info = fragInfo[senderAddr];
            if (info.msgId == 0) {
                info.msgId = msgId;
                info.data.clear();
            }
            if (info.msgId != msgId) {
                ASSERT(msgId > info.msgId);
                Warning("Failed to reconstruct packet %lx", info.msgId);
                info.msgId = msgId;
                info.data.clear();
            }
            
            if (fragStart != info.data.size()) {
                Warning("Fragments out of order for packet %lx; "
                        "expected start %zd, got %zd",
                        msgId, info.data.size(), fragStart);
                continue;
            }
            
            info.data.append(string(ptr, buf+sz-ptr));
            if (info.data.size() == msgLen) {
                Debug("Completed packet reconstruction");
                DecodePacket(info.data.c_str(), info.data.size(),
                             msgType, msg);
                info.msgId = 0;
                info.data.clear();
            } else {
                continue;
            }
        }
        
        // Dispatch
        if (dropRate > 0.0) {
            double roll = uniformDist(randomEngine);
            if (roll < dropRate) {
                Debug("Simulating packet drop of message type %s",
                      msgType.c_str());
                continue;
            }
        }

        if (!reorderBuffer.valid && (reorderRate > 0.0)) {
            double roll = uniformDist(randomEngine);
            if (roll < reorderRate) {
                Debug("Simulating reorder of message type %s",
                      msgType.c_str());
                ASSERT(!reorderBuffer.valid);
                reorderBuffer.valid = true;
                reorderBuffer.addr = new UDPTransportAddress(senderAddr);
                reorderBuffer.message = msg;
                reorderBuffer.msgType = msgType;
                reorderBuffer.fd = fd;
                continue;
            }
        }

    deliver:
        // Was this received on a multicast fd?
        auto it = multicastConfigs.find(fd);
        if (it != multicastConfigs.end()) {
            // If so, deliver the message to all replicas for that
            // config, *except* if that replica was the sender of the
            // message.
            const transport::Configuration *cfg = it->second;
            for (auto &kv : replicaReceivers[cfg]) {
                TransportReceiver *receiver = kv.second;
                const UDPTransportAddress &raddr = 
                    replicaAddresses[cfg].find(kv.first)->second;
                // Don't deliver a message to the sending replica
                if (raddr != senderAddr) {
                    receiver->ReceiveMessage(senderAddr, msgType, msg);
                }
            }
        } else {
            TransportReceiver *receiver = receivers[fd];
            receiver->ReceiveMessage(senderAddr, msgType, msg);
        }

        if (reorderBuffer.valid) {
            reorderBuffer.valid = false;
            msg = reorderBuffer.message;
            msgType = reorderBuffer.msgType;
            fd = reorderBuffer.fd;
            senderAddr = *(reorderBuffer.addr);
            delete reorderBuffer.addr;
            Debug("Delivering reordered packet of type %s",
                  msgType.c_str());
            goto deliver;       // XXX I am a bad person for this.
        }
    }
}

int
UDPTransport::Timer(uint64_t ms, timer_callback_t cb)
{
    std::lock_guard<std::mutex> lck (mtx);

    UDPTransportTimerInfo *info = new UDPTransportTimerInfo();

    struct timeval tv;
    tv.tv_sec = ms/1000;
    tv.tv_usec = (ms % 1000) * 1000;
    
    ++lastTimerId;
    
    info->transport = this;
    info->id = lastTimerId;
    info->cb = cb;
    info->ev = event_new(libeventBase, -1, 0,
                         TimerCallback, info);

    if (info->ev == NULL) {
        Debug("Error creating new Timer event : %d", lastTimerId);
    }

    timers[info->id] = info;
    
    int ret = event_add(info->ev, &tv);
    if (ret != 0) {
        Debug("Error adding new Timer event to eventbase %d", lastTimerId);
    }
    
    return info->id;
}

bool
UDPTransport::CancelTimer(int id)
{
    std::lock_guard<std::mutex> lck (mtx);

    UDPTransportTimerInfo *info = timers[id];

    if (info == NULL) {
        return false;
    }

    event_del(info->ev);
    event_free(info->ev);
    
    timers.erase(info->id);


    delete info;
    
    return true;
}

void
UDPTransport::CancelAllTimers()
{
    Debug("Cancelling all Timers");
    while (!timers.empty()) {
        auto kv = timers.begin();
        CancelTimer(kv->first);
    }
}

void
UDPTransport::OnTimer(UDPTransportTimerInfo *info)
{
    {
        std::lock_guard<std::mutex> lck (mtx);

        timers.erase(info->id);
        event_del(info->ev);
        event_free(info->ev);
    }

    info->cb();

    delete info;
}

void
UDPTransport::SocketCallback(evutil_socket_t fd, short what, void *arg)
{
    UDPTransport *transport = (UDPTransport *)arg;
    if (what & EV_READ) {
        transport->OnReadable(fd);
    }
}

void
UDPTransport::TimerCallback(evutil_socket_t fd, short what, void *arg)
{
    UDPTransport::UDPTransportTimerInfo *info =
        (UDPTransport::UDPTransportTimerInfo *)arg;

    ASSERT(what & EV_TIMEOUT);

    info->transport->OnTimer(info);
}

void
UDPTransport::LogCallback(int severity, const char *msg)
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
UDPTransport::FatalCallback(int err)
{
    Panic("Fatal libevent error: %d", err);
}

void
UDPTransport::SignalCallback(evutil_socket_t fd, short what, void *arg)
{
    Notice("Terminating on SIGTERM/SIGINT");
    UDPTransport *transport = (UDPTransport *)arg;
    event_base_loopbreak(transport->libeventBase);
}
