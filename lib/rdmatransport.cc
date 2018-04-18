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

const uint32_t MAGIC = 0x06121983;

using std::pair;

RDMATransportAddress::RDMATransportAddress(const sockaddr_in &addr)
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
        event_add(evsignal_new(libeventBase, SIGTERM,
                               SignalCallback, this),
                  NULL);
        event_add(evsignal_new(libeventBase, SIGINT,
                               SignalCallback, this),
                  NULL);

        event_add(evsignal_new(libeventBase, SIGSEGV,
                               SignalCallback, this),
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
    struct sockaddr_in sin;
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
    ASSERT(ai->ai_family == AF_INET);
    if (ai->ai_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");        
    }
    sin = *(sockaddr_in *)ai->ai_addr;
    RDMATransportAddress out =
              RDMATransportAddress(sin);
    // Don't need to free for rdma?
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

int
RDMATransport::PostReceive(RDMATransportRDMAListener *info)
{
    // post receive
    struct ibv_recv_wr wr, *bad_wr = NULL;
    struct ibv_sge sge;

    memset(info->recvPtr, 0, 400);
    memset(&wr, 0, sizeof(wr));
    wr.wr_id = (uint64_t)info->recvPtr;
    wr.sg_list = &sge;
    wr.next = NULL;
    wr.num_sge = 1;
    sge.addr = (uintptr_t)info->recvPtr;
    sge.length = 400;
    sge.lkey = info->recvmr->lkey;

    // set up next ptr
    if (info->recvPtr + 800 > info->recvData + MAX_RDMA_SIZE) {
        info->recvPtr = (char *)&info->recvData;
    } else {
        info->recvPtr += 400;
    }
    return ibv_post_recv(info->id->qp, &wr, &bad_wr);
}

void
RDMATransport::CleanupConnection(RDMATransportRDMAListener *info)
{
    if (info->cmevent) {
        // listening port
        event_free(info->cmevent);
    }
    
    if (info->cqevent) {
        event_free(info->cqevent);
        ibv_dereg_mr(info->sendmr);
        ibv_dereg_mr(info->recvmr);

        // rdma_destroy_qp(info->id);
        //ibv_destroy_comp_channel(info->cq->channel);
        //ibv_destroy_cq(info->cq);
        //ibv_dealloc_pd(info->pd);
    }
    
    //rdma_destroy_id(info->id);
    delete info;
}

RDMATransportAddress*
RDMATransport::BindToPort(struct rdma_cm_id *id, const string &host, const string &port)
{
     struct sockaddr_in sin;
    int res;
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family   = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = 0;
    hints.ai_flags    = AI_PASSIVE;
    struct addrinfo *ai;
    if ((res = getaddrinfo(host.c_str(), port.c_str(),
                           &hints, &ai))) {
        Panic("Failed to resolve %s:%s: %s",
              host.c_str(), port.c_str(), gai_strerror(res));
    }
    if (ai->ai_addr->sa_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");
    }
    ASSERT(ai->ai_family == AF_INET);
    if (ai->ai_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");        
    }
    sin = *(sockaddr_in *)ai->ai_addr;
    Debug("Binding to %s %d RDMA", inet_ntoa(sin.sin_addr), htons(sin.sin_port));

    if (rdma_bind_addr(id, (sockaddr *)&sin) < 0) {
        PPanic("Failed to bind to RDMA channel");
    }
    freeaddrinfo(ai);
    return new RDMATransportAddress(sin);
}

void
RDMATransport::ConnectRDMA(TransportReceiver *src,
                           const RDMATransportAddress &dst)
{
    int res;
    struct rdma_conn_param params;    
    struct rdma_cm_id *id;
    struct rdma_cm_event *event;
    struct rdma_event_channel *channel;

    // Create a RDMA channel for events on this link
    if((channel = rdma_create_event_channel()) == 0) {
        Panic("Could not create RDMA event channel: %s", strerror(errno));
    }
    
    // Create a communications manager for this link
    if ((rdma_create_id(channel, &id, NULL, RDMA_PS_TCP)) != 0) {
        Panic("Could not create RDMA event id");
    }

    // Convert regular address into an rdma address
    if ((res = rdma_resolve_addr(id, NULL, (sockaddr*)&dst.addr,1)) != 0) {
        Panic("Could not resolve IP to an RDMA address: %s", strerror(errno));
    }

    // Wait for address resolution
    rdma_get_cm_event(channel, &event);
    if (event->event != RDMA_CM_EVENT_ADDR_RESOLVED) {
        Panic("Could not resolve to RDMA address");
    }
    rdma_ack_cm_event(event);

    // set up connection queue pairs and info
    ConnectRDMA(src, dst, id);

    // Find path to rdma address
    if ((res = rdma_resolve_route(id, 1)) != 0) {
        Panic("Could not resolve route to RDMA address: %s", strerror(errno));
    }

    // Wait for path resolution
    rdma_get_cm_event(channel, &event);
    if (event->event != RDMA_CM_EVENT_ROUTE_RESOLVED) {
        Panic("Could not resolve route to RDMA address");
    }
    rdma_ack_cm_event(event);

    // Get channel
    memset(&params, 0, sizeof(params));
    params.initiator_depth = params.responder_resources = 1;
    params.rnr_retry_count = 7; /* infinite retry */
    
    if ((res = rdma_connect(id, &params)) != 0) {
        Panic("Could not connect RDMA: %s", strerror(errno));
    }

    // Wait for rdma connection setup to complete
    rdma_get_cm_event(channel, &event);
    if (event->event != RDMA_CM_EVENT_ESTABLISHED) {
        Panic("Could not connect to RDMA address ");
    }
    rdma_ack_cm_event(event);

    auto kv = rdmaOutgoing.find(dst);
    ASSERT(kv->second != NULL);    
    RDMATransportRDMAListener *info = kv->second;

    int fd = channel->fd;
    // set up call back
    
    int flags = fcntl(fd, F_GETFL);
    if (fcntl(fd, F_SETFL, flags | O_NONBLOCK)) {
        Panic("Failed to set O_NONBLOCK");
    }

    // Create a libevent event for the event channel
    info->cmevent = event_new(libeventBase,
                              info->id->channel->fd,
                              EV_READ | EV_PERSIST,
                              &RDMAIncomingCallback,
                              (void *)info);
    event_add(info->cmevent, NULL);

}

void
RDMATransport::ConnectRDMA(TransportReceiver *src,
                           const RDMATransportAddress &dst,
                           struct rdma_cm_id *id)
{
    RDMATransportRDMAListener *info = new RDMATransportRDMAListener();
    struct ibv_qp_init_attr qp_attr;
    struct ibv_comp_channel *channel;
        
    // Set up our needed info for this connection
    info->transport = this;
    info->receiver = src;
    info->id = id;
        
    // Set up new queue pairs
    // Allocate a protection domain
    if ((info->pd = ibv_alloc_pd(id->verbs)) == NULL) {
        delete info;
        Panic("Failed to allocate pd");
    }
    // Create a completion channel
    if ((channel = ibv_create_comp_channel(id->verbs)) == NULL) {
        Panic("Could not create completion channel");
    }
    // Create a completion queue
    if ((info->cq = ibv_create_cq(id->verbs, 10, NULL, channel, 0)) == NULL) {
        Panic("Could not create completion channel");
    }
    // Set up the completion queue to notify on the channel for any events
    if (ibv_req_notify_cq(info->cq, 0) != 0) {
        Panic("Can't set up notifications");
    }

    // Set up queue pair initial parameters
    memset(&qp_attr, 0, sizeof(qp_attr));
    qp_attr.send_cq = info->cq;
    qp_attr.recv_cq = info->cq;
    qp_attr.qp_type = IBV_QPT_RC;
    qp_attr.cap.max_send_wr = 20;
    qp_attr.cap.max_recv_wr = 20;
    qp_attr.cap.max_send_sge = 1;
    qp_attr.cap.max_recv_sge = 1;
    if (rdma_create_qp(id, info->pd, &qp_attr) != 0) {
        Panic("Could not create RDMA queue pair: %s", strerror(errno));
    }

    info->id->send_cq_channel = channel;
    info->id->recv_cq_channel = channel;
    info->id->send_cq = info->cq;
    info->id->recv_cq = info->cq;
    // Register memory for communications
    if ((info->sendmr = ibv_reg_mr(info->pd,
                                   &info->sendData,
                                   MAX_RDMA_SIZE,
                                   IBV_ACCESS_LOCAL_WRITE)) == 0) {
        Panic("Could not register send buffer");
    }
    
    if ((info->recvmr = ibv_reg_mr(info->pd,
                                   &info->recvData,
                                   MAX_RDMA_SIZE,
                                   IBV_ACCESS_LOCAL_WRITE | IBV_ACCESS_REMOTE_WRITE)) == 0) {
        Panic("Could not register receive buffer");
    }
    info->sendPtr = (char *)&info->sendData;
    info->recvPtr = (char *)&info->recvData;

    // Put the connection in non-blocking mode
    int fd = channel->fd;
    int flags = fcntl(fd, F_GETFL);
    if (fcntl(fd, F_SETFL, flags | O_NONBLOCK)) {
        Panic("Failed to set O_NONBLOCK");
    }

    // finish set up for new connection
    if (PostReceive(info) != 0) {
        Panic("Can't post receive for %s:%u",
              inet_ntoa(dst.addr.sin_addr),
              dst.addr.sin_port);
    }
    if (PostReceive(info) != 0) {
        Panic("Can't post receive for %s:%u",
              inet_ntoa(dst.addr.sin_addr),
              dst.addr.sin_port);
    }
    if (PostReceive(info) != 0) {
        Panic("Can't post receive for %s:%u",
              inet_ntoa(dst.addr.sin_addr),
              dst.addr.sin_port);
    }
        
    // Create an libevent event for the completion channel
    info->cqevent = event_new(libeventBase,
                              fd,
                              EV_READ | EV_WRITE | EV_PERSIST,
                              &RDMAReadableCallback,
                              (void *)info);
    event_add(info->cqevent, NULL);

    // Tell the receiver its address
    struct sockaddr_in sin;
    memset(&sin, 0, sizeof(sin));
    RDMATransportAddress *addr = new RDMATransportAddress(sin);
    src->SetAddress(addr);

    // Set up mappings
    info->transport->rdmaOutgoing[dst] = info;
    info->transport->rdmaAddresses.insert(pair<struct RDMATransportRDMAListener *, RDMATransportAddress>(info,dst));
    Debug("Connected to: %s:%u",
          inet_ntoa(dst.addr.sin_addr),
          dst.addr.sin_port);
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
        Debug("Clients do not need to listen for RDMA conections");
        return;
    }
    
    struct rdma_cm_id *acceptID;
    struct rdma_event_channel *channel;

    // Create a RDMA channel for events on this link
    if((channel = rdma_create_event_channel()) == 0) {
        Panic("Could not create RDMA event channel: %s", strerror(errno));
    }

    if ((rdma_create_id(channel, &acceptID, NULL, RDMA_PS_TCP)) != 0) {
        Panic("Could not create RDMA event id: %s", strerror(errno));
    }
    
    //get file descriptor
    int fd = channel->fd;
    // Put it in non-blocking mode
    int flags = fcntl(channel->fd, F_GETFL);
    if (fcntl(channel->fd, F_SETFL, flags | O_NONBLOCK)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Registering a replica. Bind socket to the designated
    // host/port
    const string &host = config.replica(replicaIdx).host;
    const string &port = config.replica(replicaIdx).port;
    RDMATransportAddress *addr = BindToPort(acceptID, host, port);
    
    // Listen for connections
    if (rdma_listen(acceptID, 10) != 0) {
        PPanic("Failed to listen for RDMA connections");
    }
        
    // Set up our own info for this connection
    RDMATransportRDMAListener *info = new RDMATransportRDMAListener();
    info->transport = this;
    info->receiver = receiver;
    info->id = acceptID;
    info->cmevent = event_new(libeventBase, fd,
                              EV_READ | EV_PERSIST,
                              RDMAIncomingCallback, (void *)info);
    event_add(info->cmevent, NULL);
    
    // Tell the receiver its address
    
    receiver->SetAddress(addr);

    Debug("Accepting connections on RDMA port %s", port.c_str());
}

bool
RDMATransport::SendMessageInternal(TransportReceiver *src,
                                  const RDMATransportAddress &dst,
                                  const Message &m,
                                  bool multicast)
{
    auto kv = rdmaOutgoing.find(dst);
    struct RDMATransportRDMAListener *info;
    
    // See if we have a connection open
    if (kv == rdmaOutgoing.end()) {
        // if not open one
        ConnectRDMA(src, dst);
    }

    kv = rdmaOutgoing.find(dst);
    ASSERT(kv->second != NULL);    
    info = kv->second;

    // get message info
    string type = m.GetTypeName();
    string data = m.SerializeAsString();
    size_t typeLen = type.length();
    size_t dataLen = data.length();
    size_t totalLen = (typeLen + sizeof(typeLen) +
                       dataLen + sizeof(dataLen) +
                       sizeof(totalLen) +
                       sizeof(uint32_t));
    
    ASSERT(totalLen < MAX_RDMA_SIZE);

    // allocate buffer
    if (info->sendPtr + totalLen > (char *)&info->sendData + MAX_RDMA_SIZE) {
        info->sendPtr = (char *)&info->sendData;
    }
    char *ptr = info->sendPtr;

    *((uint32_t *) ptr) = MAGIC;
    ptr += sizeof(uint32_t);
    *((size_t *) ptr) = totalLen;
    ptr += sizeof(size_t);
    *((size_t *) ptr) = typeLen;
    ptr += sizeof(size_t);
    memcpy(ptr, type.c_str(), typeLen);
    ptr += typeLen;
    *((size_t *) ptr) = dataLen;
    ptr += sizeof(size_t);
    memcpy(ptr, data.c_str(), dataLen);
    ptr += dataLen;
    ASSERT(ptr - info->sendPtr == totalLen);
    
    // set up message
    struct ibv_send_wr wr, *bad_wr = NULL;
    struct ibv_sge sge;
    memset(&wr, 0, sizeof(wr));
    wr.wr_id = (uint64_t)&info->sendPtr;
    wr.opcode = IBV_WR_SEND;
    wr.sg_list = &sge;
    wr.num_sge = 1;
    wr.send_flags = IBV_SEND_SIGNALED;// | IBV_SEND_INLINE;
    wr.next = NULL;

    sge.addr = (uintptr_t)info->sendPtr;
    sge.length = totalLen;
    sge.lkey = info->sendmr->lkey;

    // move up for next message
    if (ptr > (char *)&info->sendData + MAX_RDMA_SIZE) {
        info->sendPtr = (char *)&info->sendData;
    } else {
        info->sendPtr = ptr;
    }
    
    if (ibv_post_send(info->id->qp, &wr, &bad_wr) != 0) {
        Panic("Could not send message: %s", strerror(errno));
    }
    
    return true;
}

void
RDMATransport::Run()
{
    Debug("Running event base");
    event_base_dispatch(libeventBase);
}

void
RDMATransport::Stop()
{
    Debug("Event loop stopped");
    event_base_loopbreak(libeventBase);
}

int
RDMATransport::Timer(uint64_t ms, timer_callback_t cb)
{
    if (ms == 0) {
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
    
        return lastTimerId;
    }
    return 0;
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
RDMATransport::RDMAIncomingCallback(evutil_socket_t fd, short what, void *arg)
{
    RDMATransportRDMAListener *info = (RDMATransportRDMAListener *)arg;
    RDMATransport *transport = info->transport;
    struct rdma_cm_event *event;

    //check no block
    ASSERT(fcntl(info->id->channel->fd, F_GETFL) & O_NONBLOCK);
    // if we found an event
    if (rdma_get_cm_event(info->id->channel, &event) == 0) {
        sockaddr_in *sin = (sockaddr_in *)rdma_get_peer_addr(event->id);
        RDMATransportAddress addr(*sin);

        if (transport->rdmaOutgoing.find(addr) == transport->rdmaOutgoing.end()) {
            // can't find connection, so must be a new one
            ASSERT(event->event == RDMA_CM_EVENT_CONNECT_REQUEST);

            Debug("Accept callback from: %s:%u",
                  inet_ntoa(sin->sin_addr),
                  sin->sin_port);
            // Set up queue pairs for the new connection
            transport->ConnectRDMA(info->receiver, addr, event->id);
            // Do no need to add libevent because the new connection
            // shares a cm event queue with the listening socket
        }
        
        info = transport->rdmaOutgoing[addr];
        ASSERT(info != NULL);

        ASSERT(info->id = event->id);

        switch(event->event) {
        case RDMA_CM_EVENT_CONNECT_REQUEST:
        {
            // Accept the connection
            struct rdma_conn_param params;
            memset(&params, 0, sizeof(params));
            params.initiator_depth = params.responder_resources = 1;
            params.rnr_retry_count = 7; /* infinite retry */
            if ((rdma_accept(event->id, &params)) != 0) {
                PWarning("Failed to accept incoming RDMA connection: %s",
                         strerror(errno));
            }
            break;
        }
        case RDMA_CM_EVENT_DISCONNECTED:
        {
            Debug("EOF on %s:%u",
                  inet_ntoa(sin->sin_addr),
                  sin->sin_port);
            CleanupConnection(info);
            transport->rdmaOutgoing.erase(addr);
            auto it2 = transport->rdmaAddresses.find(info);
            transport->rdmaAddresses.erase(it2);
            break;
        }
        case RDMA_CM_EVENT_ESTABLISHED:
        {
            Debug("Opened incoming RDMA connection: %s:%u",
                  inet_ntoa(sin->sin_addr),
                  sin->sin_port);

            break;
        }
        case RDMA_CM_EVENT_ROUTE_RESOLVED:
        case RDMA_CM_EVENT_ADDR_RESOLVED:
            Debug("Route or addr resolved");
            break;
        default:
            Debug("Unexpected event on listening socket: %u", event->event);
            // ignore
        }
        rdma_ack_cm_event(event);
    }
}

void
RDMATransport::RDMAReadableCallback(evutil_socket_t fd, short what, void *arg)
{
    RDMATransportRDMAListener *info = (RDMATransportRDMAListener *)arg;
    RDMATransport *transport = info->transport;
    struct ibv_cq *cq;
    struct ibv_context *context;
    ASSERT(fcntl(info->cq->channel->fd, F_GETFL) & O_NONBLOCK);
    int numEvents = 0;
    
    while (ibv_get_cq_event(info->cq->channel, &cq, (void**)&context) == 0) {
        numEvents++;
    }

    ibv_ack_cq_events(cq, numEvents);
    if (ibv_req_notify_cq(cq, 0) != 0) {
        Panic("Can't set up notifications");
    }
        
    struct ibv_wc wc;
    while (ibv_poll_cq(cq, 1, &wc) > 0) {
        if (wc.status == IBV_WC_SUCCESS) {
            switch (wc.opcode) {
            case IBV_WC_SEND:
            {
                Debug("Successfully sent %u bytes over RDMA",
                      wc.byte_len);
                break;                
            }
            case IBV_WC_RECV:
            {
                // Post receive to get the next packet
                if (PostReceive(info) != 0) {
                    Warning("Sent message but failed to post receive for reply");
                }
                auto addr = transport->rdmaAddresses.find(info);
                ASSERT(addr != transport->rdmaAddresses.end());
                Debug("Received %u bytes over RDMA", wc.byte_len);
                char *ptr = (char *)wc.wr_id;
                uint32_t magic = *((uint32_t *)ptr);

                if (magic != MAGIC) {
                    Warning("No Magic: %u bytes sent: %u", magic, wc.byte_len);
                    break;
                }

                ptr += sizeof(magic);
                size_t totalSize = *((size_t *)ptr);
                ASSERT(totalSize < MAX_RDMA_SIZE);
                ptr += sizeof(totalSize);
                size_t typeLen = *((size_t *)ptr);
                ptr += sizeof(typeLen);
                string type(ptr, typeLen);
                ptr += typeLen;
                size_t msgLen = *((size_t *)ptr);
                ptr += sizeof(msgLen);
                string data(ptr, msgLen);;

                // Dispatch
                info->receiver->ReceiveMessage(addr->second,
                                               type,
                                               data);
                Debug("Done processing %s message",
                      type.c_str());
               
                break;
            }
            default:
                //ignore
                break;
            }
        } else {
            Warning("Something failed!");
        }
    }

}
