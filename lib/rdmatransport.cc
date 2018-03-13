// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * rdmatransport.cc:
 *   message-passing network interface that uses RDMA message delivery
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
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISINg FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 **********************************************************************/

#include "lib/assert.h"
#include "lib/configuration.h"
#include "lib/message.h"
#include "lib/rdmatransport.h"

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

const size_t MAX_RDMA_SIZE = 100; // XXX
const uint32_t MAGIC = 0x06121983;

using std::pair;

RDMATransportAddress::RDMATransportAddress(const rdma_addrinfo &addr)
    : addr(addr)
{
    memset((void *)addr.sin_zero, 0, sizeof(addr.sin_zero));
}

RDMATransportAddress *
RDMATransportAddress::clone() const
{
    RDMATransportAddress *c = new RDMATransportAddress(*this);
    return c;    
}

bool operator==(const RDMATransportAddress &a, const RDMATransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) == 0);
}

bool operator!=(const RDMATransportAddress &a, const RDMATransportAddress &b)
{
    return !(a == b);
}

bool operator<(const RDMATransportAddress &a, const RDMATransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) < 0);
}

RDMATransport::RDMATransport(double dropRate, double reorderRate,
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
        event_add((evsignal_new(libeventBase, SIGTERM,
                                SignalCallback, this),
                      NULL);
        event_add(evsignal_new(libeventBase, SIGINT,
                               SignalCallback, this)
            NULL);
    }
}

RDMATransport::~RDMATransport()
{
    // XXX Shut down libevent?

    // for (auto kv : timers) {
    //     delete kv.second;
    // }
}


RDMATransportAddress
RDMATransport::LookupAddress(const transport::ReplicaAddress &addr)
{
        int res;
        struct rdma_addrinfo hints;
        hints.ai_family   = AF_INET;
        hints.qp_type = IBV_RC;
        hints.ai_flags    = 0;
        struct rdma_addrinfo *ai;
        if ((res = rdma_getaddrinfo(addr.host.c_str(), addr.port.c_str(),
                                    &hints, &ai))) {
            Panic("Failed to resolve %s:%s: %s",
                  addr.host.c_str(), addr.port.c_str(), gai_strerror(res));
        }
        if (ai->ai_addr->sa_family != AF_INET) {
            Panic("getaddrinfo returned a non IPv4 address");
        }
        RDMATransportAddress out =
              RDMATransportAddress(*((sockaddr_in *)ai->ai_dst_addr));
        freeaddrinfo(ai);
        return out;
}

RDMATransportAddress
RDMATransport::LookupAddress(const transport::Configuration &config,
                            int idx)
{
    const transport::ReplicaAddress &addr = config.replica(idx);
    return LookupAddress(addr);
}

static void
BindToPort(struct rdma_cm_id *id, const string &host, const string &port)
{
    struct sockaddr_in sin;
    
    // look up its hostname and port number (which
    // might be a service name)
    struct rdma_addrinfo hints;
    hints.ai_family   = AF_INET;
    hints.qp_type = IBV_RC;
    hints.ai_flags    = AI_PASSIVE;
    struct addrinfo *ai;
    int res;
    if ((res = rdma_getaddrinfo(host.c_str(),
                                port.c_str(),
                                &hints, &ai))) {
        Panic("Failed to resolve host/port %s:%s: %s",
              host.c_str(), port.c_str(), gai_strerror(res));
    }
    ASSERT(ai->ai_family == AF_INET);
    if (ai->ai_addr->sa_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");        
    }
    sin = *(sockaddr_in *)ai->ai_dst_addr;
        
    freeaddrinfo(ai);

    Debug("Binding to %s %d RDMA", inet_ntoa(sin.sin_addr), htons(sin.sin_port));

    if (rdma_bind_addr(id, (sockaddr *)&sin, sizeof(sin)) < 0) {
        PPanic("Failed to bind to RDMA channel");
    }
}

void
RDMATransport::ConnectRDMA(TransportReceiver *src,
                           RDMATransportAddress &dst)
{
    int res;
    struct rdma_cm_id *id;
    
    if ((rdma_create_id(NULL, &id, NULL, RDMA_PS_TCP)) != 0) {
        Panic("Could not create RDMA event id");
    }

    res = rdma_resolve_addr(id, NULL,(sockaddr)dst.addr,1);
    ASSERT(res == 0);
    res = rdma_resolve_route(id, 1);
    ASSERT(res == 0);
    
    //get file descriptor
    int fd = ec->fd;
    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    ConnectRDMA(src, id);
}

void
RDMATransport::ConnectRDMA(TransportReceiver *src,
                           struct rdma_cm_id *dst)
{
    RDMATransportRDMAListener *info = new RDMATransportRDMAListener();
    struct ibv_qp_init_attr *qp_attr;
    struct event *ev;
    struct ibv_pd *pd;
    int res;

    // Set up info
    info->transport = this;
    info->id = dst;
    info->receiver = src;
    info->replicaIdx = -1;
    info->acceptEvent = NULL;
        
    // Create new RDMA channel
    pd = ibv_alloc_pd(dst->verbs);
    params->initiator_depth = params->responder_resources = 1;
    params->rnr_retry_count = 7; /* infinite retry */
    qp_attr->qp_type = IBV_QPT_RC;
    qp_attr->cap.max_send_wr = 10;
    qp_attr->cap.max_recv_wr = 10;
    qp_attr->cap.max_send_sge = 1;
    qp_attr->cap.max_recv_sge = 1;
    res = rdma_create_qp(id, pd, &qp_attr);
    ASSERT(res == 0);

    // register memory
    if ((info->sendmr = ibv_reg_mr(info->pd,
                                   &info->send,
                                   sizeof(Message),
                                   IBV_ACCESS_LOCAL_WRITE)) == 0) {
        Panic("Could not register send buffer");
    }

    if ((info->recvmr = ibv_reg_mr(info=>pd,
                                   info->recv,
                                   sizeof(Message),
                                   IBV_ACCESS_LOCAL_WRITE | IBV_ACCESS_REMOTE_WRITE))== 0) {
        Panic("Could not register receive buffer");
    }

    // Put the connection in non-blocking mode
    if (fcntl(dst->channel->fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Create an event
    struct event *ev = event_new(libeventBase, dst->channel->fd,
                                 EV_READ|EV_WRITE,
                                 RDMAReadableCallback, (void *)info);
    event_add(ev, NULL);
    info->connectionEvents.push_back(ev);
    

	transport->rdmaOutgoing[dst] = ev; 
	transport->rdmaAddresses.insert(pair<struct event*, RDMATransportAddress>(ev,dst));
}

void
RDMATransport::Register(TransportReceiver *receiver,
                       const transport::Configuration &config,
                       int replicaIdx)
{
    ASSERT(replicaIdx < config.n);
    RegisterConfiguration(receiver, config, replicaIdx);

    // Clients don't need to accept RDMA connections
    if (replicaIdx == -1) {
        return;
    }
    
    // Create a RDMA channel
    struct rdma_event_channel *ec = NULL;
    if((ec = rdma_create_event_channel()) == 0) {
        Panic("Could not create RDMA event channel");
    }
    struct rdma_cm_id *listener = NULL;
    if ((rdma_create_id(ec, &listener, NULL, RDMA_PS_TCP)) != 0) {
        Panic("Could not create RDMA event id");
    }
    //get file descriptor
    int fd = ec->fd;
    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Registering a replica. Bind socket to the designated
    // host/port
    const string &host = config.replica(replicaIdx).host;
    const string &port = config.replica(replicaIdx).port;
    BindToPort(listener, host, port);
    
    // Listen for connections
    if (rdma_listen(listener, 10) < 0) {
        PPanic("Failed to listen for RDMA connections");
    }
        
    // Create event to accept connections
    RDMATransportRDMAConnection *info = new RDMATransportRDMAConnection();
    info->transport = this;
    info->receiver = receiver;
    info->id = listener;
    info->replicaIdx = replicaIdx;
    event_add(event_new(libeventBase, fd,
                        EV_READ | EV_PERSIST,
                        RDMAAcceptCallback, (void *)info),
              NULL);
    rdmaConnections.push_back(info);

    // Tell the receiver its address
    struct sockaddr_in sin;
    socklen_t sinsize = sizeof(sin);
    if (getsockname(fd, (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    RDMATransportAddress *addr = new RDMATransportAddress(sin);
    receiver->SetAddress(addr);

    Debug("Accepting connections on RDMA port %hu", ntohs(sin.sin_port));
}

bool
RDMATransport::SendMessageInternal(TransportReceiver *src,
                                  const RDMATransportAddress &dst,
                                  const Message &m,
                                  bool multicast)
{
    auto kv = rdmaOutgoing.find(dst);
    // See if we have a connection open
    if (kv == rdmaOutgoing.end()) {
        ConnectRDMA(src, dst);
        kv = rdmaOutgoing.find(dst);
    }
    
    struct event *ev = kv->second;
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

    Debug("Sending %ld byte %s message to server over RDMA",
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

    if (event_write(ev, buf, totalLen) < 0) {
        Warning("Failed to write to RDMA buffer");
        return false;
    }
    
    return true;
}

void
RDMATransport::Run()
{
    event_base_dispatch(libeventBase);
}

void
RDMATransport::Stop()
{
    event_base_loopbreak(libeventBase);
}

int
RDMATransport::Timer(uint64_t ms, timer_callback_t cb)
{
    std::lock_guard<std::mutex> lck(mtx);
    
    RDMATransportTimerInfo *info = new RDMATransportTimerInfo();

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
RDMATransport::CancelTimer(int id)
{
    std::lock_guard<std::mutex> lck(mtx);
    RDMATransportTimerInfo *info = timers[id];

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
RDMATransport::CancelAllTimers()
{
    while (!timers.empty()) {
        auto kv = timers.begin();
        CancelTimer(kv->first);
    }
}

void
RDMATransport::OnTimer(RDMATransportTimerInfo *info)
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
RDMATransport::TimerCallback(evutil_socket_t fd, short what, void *arg)
{
    RDMATransport::RDMATransportTimerInfo *info =
        (RDMATransport::RDMATransportTimerInfo *)arg;

    ASSERT(what & EV_TIMEOUT);

    info->transport->OnTimer(info);
}

void
RDMATransport::LogCallback(int severity, const char *msg)
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
RDMATransport::FatalCallback(int err)
{
    Panic("Fatal libevent error: %d", err);
}

void
RDMATransport::SignalCallback(evutil_socket_t fd, short what, void *arg)
{
    Debug("Terminating on SIGTERM/SIGINT");
    RDMATransport *transport = (RDMATransport *)arg;
    event_base_loopbreak(transport->libeventBase);
}


void
RDMATransport::RDMAListenerCallback(evutil_socket_t fd, short what, void *arg)
{
    RDMATransportRDMAConnection *info = (RDMATransportRDMAListener *)arg;
    struct rdma_cm_event *ev;
    rdma_cm_get_event(info->channel, &event);

    switch(ev->event) {
    case RDMA_CM_EVENT_CONNECT_REQUEST:
        RDMAAcceptCallback(ev);
        return;
    case RDMA_CM_EVENT_ESTABLISHED:
        // set a flag?
        Warning("Connection established on outgoing RDMA connection");
        return;
    case RDMA_CM_EVENT_DISCONNECTED:
        Warning("EOF on outgoing RDMA connection to server");
        event_free(bev);
        auto it2 = transport->rdmaOutgoing.find(addr);
        transport->rdmaOutgoing.erase(it2);
        transport->rdmaAddresses.erase(bev);
        return;
    }
}

void
RDMATransport::RDMAAcceptCallback(RDMATransportRDMALIstener *info,
                                  struct rdma_cm_event *event)
{
    RDMATransport *transport = info->transport;
    struct rdma_conn_param param;

    // Accept a connection
    if ((rdma_accept(event->listen_id, &param)) < 0) {
        PWarning("Failed to accept incoming RDMA connection");
        rdma_ack_cm_event(event);
        return;
    }
    
    ConnectRDMA(transport, event->id);
    rdma_ack_cm_event(event);
    Debug("Opened incoming RDMA connection from %s:%d",
          rdma_get_dst_addr(event->id),
          rdma_get_dst_port(event->id));
}

void
RDMATransport::RDMAReadableCallback(struct event *bev, void *arg)
{
    RDMATransportRDMAListener *info = (RDMATransportRDMAListener *)arg;
    RDMATransport *transport = info->transport;
    struct evbuffer *evbuf = event_get_input(bev);

    Debug("Readable on event %p", bev);
    
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

    auto addr = transport->rdmaAddresses.find(bev);
    ASSERT(addr != transport->rdmaAddresses.end());

    // Dispatch
    info->receiver->ReceiveMessage(addr->second, msgType, msg);
    Debug("Done processing large %s message", msgType.c_str());
}

void
RDMATransport::RDMAIncomingEventCallback(struct event *ev,
                                         short what, void *arg)
{
    if (what & BEV_EVENT_ERROR) {
        Warning("Error on incoming RDMA connection: %s",
                evutil_socket_error_to_string(EVUTIL_SOCKET_ERROR()));
        event_free(bev);
        return;
    } else if (what & BEV_EVENT_ERROR) {
        Warning("EOF on incoming RDMA connection");
        event_free(bev);
        return;
    }
}

void
RDMATransport::RDMAOutgoingEventCallback(struct event *ev,
                                         short what, void *arg)
{
    RDMATransportRDMAListener *info = (RDMATransportRDMAListener *)arg;
    RDMATransport *transport = info->transport;
    auto it = transport->rdmaAddresses.find(bev);    
    ASSERT(it != transport->rdmaAddresses.end());
    RDMATransportAddress addr = it->second;
    
    if (what & BEV_EVENT_CONNECTED) {
        Debug("Established outgoing RDMA connection to server");
    } else if (what & BEV_EVENT_ERROR) {
        Warning("Error on outgoing RDMA connection to server: %s",
                evutil_socket_error_to_string(EVUTIL_SOCKET_ERROR()));
        event_free(bev);
        auto it2 = transport->rdmaOutgoing.find(addr);
        transport->rdmaOutgoing.erase(it2);
        transport->rdmaAddresses.erase(bev);
        return;
    } else if (what & BEV_EVENT_EOF) {
    }
}
