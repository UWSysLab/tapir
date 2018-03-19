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
    hints.ai_qp_type = IBV_QPT_RC;
    hints.ai_flags    = 0;
    struct rdma_addrinfo *ai;
    if ((res = rdma_getaddrinfo(addr.host.c_str(), addr.port.c_str(),
                                &hints, &ai))) {
        Panic("Failed to resolve %s:%s: %s",
              addr.host.c_str(), addr.port.c_str(), gai_strerror(res));
    }
    if (ai->ai_dst_addr->sa_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");
    }
    RDMATransportAddress out =
              RDMATransportAddress(*((sockaddr_in *)ai->ai_dst_addr));
    // Don't need to free for rdma?
    //freeaddrinfo(ai);
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
    struct ibv_recv_wr wr, *bad_wr;
    struct ibv_sge sge[2];
    wr.wr_id = MAGIC;
    wr.sg_list = sge;
    wr.next = NULL;
    wr.num_sge = 2;
    
    sge[0].addr = (uintptr_t) &(info->recvType);
    sge[0].length = RDMA_MAX_STRING_SIZE;
    sge[0].lkey = info->recvmr[0]->lkey;
    sge[1].addr = (uintptr_t) &(info->recvData);
    sge[1].length = RDMA_MAX_STRING_SIZE;
    sge[1].lkey = info->recvmr[1]->lkey;
    return ibv_post_recv(info->qp, &wr, &bad_wr);
}

void
RDMATransport::CleanupConnection(RDMATransportListener *info)
{
    rdma_disconnect(info->id);
    ibv_destroy_cp(info->cp);
    ibv_destroy_comp_channel(info->channel);
    rdma_destroy_pd(info->pd);
    rdma_destroy_qp(info->qp);
    ibv_dereg_mr(info->sendmr);
    ibv_dereg_mr(info->recvmr);
    rdma_destroy_id(info->id);
    delete info;
}

static void
BindToPort(struct rdma_cm_id *id, const string &host, const string &port)
{
    struct sockaddr_in sin;
    // look up its hostname and port number (which
    // might be a service name)
    struct rdma_addrinfo hints;
    hints.ai_family   = AF_INET;
    hints.qp_type = IBV_QPT_RC;
    hints.ai_flags    = AI_PASSIVE;
    struct rdma_addrinfo *ai;
    int res;
    if ((res = rdma_getaddrinfo(host.c_str(),
                                port.c_str(),
                                &hints, &ai))) {
        Panic("Failed to resolve host/port %s:%s: %s",
              host.c_str(), port.c_str(), gai_strerror(res));
    }
    ASSERT(ai->ai_family == AF_INET);
    if (ai->ai_dst_addr->sa_family != AF_INET) {
        Panic("getaddrinfo returned a non IPv4 address");        
    }
    sin = *(sockaddr_in *)ai->ai_dst_addr;
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
    struct rdma_cm_event *event;
    struct rdma_conn_params params;
    struct RDMATransportRDMAListener *info;
    
    // create an cm id for setting up the connection
    struct rdma_cm_id *id;
    if ((rdma_create_id(NULL, &id, NULL, RDMA_PS_TCP)) != 0) {
        Panic("Could not create RDMA event id");
    }

    // convert regular address into an rdma address
    if (res = rdma_resolve_addr(id, NULL,(sockaddr)dst.addr,1)) {
        Panic("Could not resolve IP to an RDMA address");
    }

    // find path to rdma address
    if (res = rdma_resolve_route(id, 1)) {
        Panic("Could not resolve route to RDMA address");
    }

    // set up connection
    ConnectRDMA(src, dst, id);

    // Get channel
    params->initiator_depth = params->responder_resources = 1;
    params->rnr_retry_count = 7; /* infinite retry */

    if (res = rdma_connect(id, &params)) {
        Panic("Could not connect RDMA");
    }
}

void
RDMATransport::ConnectRDMA(TransportReceiver *src,
                           const RDMATransportAddress &dst,
                           struct rdma_cm_id *id)
{
    RDMATransportRDMAListener *info = new RDMATransportRDMAListener();
    struct ibv_qp_init_attr *qp_attr;
        
    // Set up our needed info
    info->transport = this;
    info->receiver = src;
    info->id = id;
        
    // set up new RDMA channel and queue pairs
    if ((info->pd = ibv_alloc_pd(id->verbs)) == NULL) {
        delete info;
        PWarning("Failed to allocate pd");
        return;
    }
    if ((info->channel = ibv_create_comp_channel) == NULL) {
        delete info;
        PWarning("Could not create completion channel");
        return;
    }
    if ((info->cq = ibv_create_cq(id->verbs, 10, NULL, info->channel, 0)) == NULL) {
        ibv_destroy_comp_channel(info->channel);
        delete info;
        PWarning("Could not create completion channel");
        return;
    }

    if (ibv_req_notify_cq(info->cq, 0) != 0) {
        Panic("Can't set up notifications");
    }
        
    qp_attr->qp_type = IBV_QPT_RC;
    qp_attr->cap.max_send_wr = 10;
    qp_attr->cap.max_recv_wr = 10;
    qp_attr->cap.max_send_sge = 1;
    qp_attr->cap.max_recv_sge = 1;
    if (rdma_create_qp(id, pd, &qp_attr) != 0) {
        Panic("Could not create RDMA queue pair");
    }

        
    // Register memory for communications
    if ((info->sendmr[0] = ibv_reg_mr(info->pd,
                                      &info->sendType,
                                      RDMA_MAX_STRING_SIZE,
                                      IBV_ACCESS_LOCAL_WRITE)) == 0) {
        Panic("Could not register send buffer");
    }
    if ((info->sendmr[1] = ibv_reg_mr(info->pd,
                                      &info->sendData,
                                      RDMA_MAX_STRING_SIZE,
                                      IBV_ACCESS_LOCAL_WRITE)) == 0) {
        Panic("Could not register send buffer");
    }
    
    if ((info->recvmr[0] = ibv_reg_mr(info->pd,
                                      &info->recvType,
                                      RDMA_MAX_STRING_SIZE,
                                      IBV_ACCESS_LOCAL_WRITE | IBV_ACCESS_REMOTE_WRITE))== 0) {
        Panic("Could not register receive buffer");
    }
    if ((info->recvmr[1] = ibv_reg_mr(info->pd,
                                      &info->recvData,
                                      RDMA_MAX_STRING_SIZE,
                                      IBV_ACCESS_LOCAL_WRITE | IBV_ACCESS_REMOTE_WRITE))== 0) {
        Panic("Could not register receive buffer");
    }

    // Put the connection in non-blocking mode
    if (fcntl(info->channel->fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Create an libevent event for the channel
    info->libevent = event_new(libeventBase, info->channel->fd,
                               EV_READ|EV_WRITE,
                               RDMAReadableCallback, (void *)info);
    event_add(info->libevent, NULL);

    // Set up mappings
    info->transport->rdmaOutgoing[dst] = info;
    info->transport->rdmaAddresses[info] = dst;
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
    struct rdma_event_channel *channel;
    if((channel = rdma_create_event_channel()) == 0) {
        Panic("Could not create RDMA event channel");
    }
    struct rdma_cm_id *acceptID;
    if ((rdma_create_id(channel, &acceptID, NULL, RDMA_PS_TCP)) != 0) {
        Panic("Could not create RDMA event id");
    }
    //get file descriptor
    int fd = channel->fd;
    // Put it in non-blocking mode
    if (fcntl(fd, F_SETFL, O_NONBLOCK, 1)) {
        PWarning("Failed to set O_NONBLOCK");
    }

    // Registering a replica. Bind socket to the designated
    // host/port
    const string &host = config.replica(replicaIdx).host;
    const string &port = config.replica(replicaIdx).port;
    BindToPort(acceptID, host, port);
    
    // Listen for connections
    if (rdma_listen(acceptID, 10) != 0) {
        PPanic("Failed to listen for RDMA connections");
    }
        
    // Set up our own info for this connection
    RDMATransportRDMAListener *info = new RDMATransportRDMAListener();
    info->transport = this;
    info->receiver = receiver;
    info->id = acceptID;
    info->libevent = event_new(libeventBase, fd,
                               EV_READ | EV_PERSIST,
                               RDMAAcceptCallback, (void *)info);
    event_add(info->libevent, NULL);
    
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
    
    struct RDMATransportRDMAListener *info = kv->second;

    // set up message
    struct ibv_send_wr wr, *bad_wr;
    struct ibv_sge sge[2];
    wr.wr_id = MAGIC;
    wr.opcode = IBV_WR_SEND;
    wr.sg_list = sge;
    wr.num_sge = 2;
    wr.send_flags = IBV_SEND_SIGNALED;

    // first, write message type
    info->sendType = m.GetTypeName();
    ASSERT(info->sendType.length() < RDMA_MAX_STRING_SIZE);
    sge[0].addr = (uintptr_t) &info->sendType;
    sge[0].length = info->sendType.length();
    sge[0].lkey = info->sendmr[0]->lkey;
    info->sendData = m.SerializeAsString();
    ASSERT(info->sendData.length() < RDMA_MAX_STRING_SIZE);
    sge[1].addr = (uintptr_t) &info->sendData;
    sge[1].length = info->sendData.length();
    sge[1].lkey = info->sendmr[1]->lkey;

    ibv_post_send(info->qp, &wr, &bad_wr);
    
    // Post receive to get the response
    if (PostReceive(info) != 0) {
        Warning("Sent message but failed to post receive for reply");
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
RDMATransport::RDMAAcceptCallback(evutil_socket_t fd, short what, void *arg)
{
    RDMATransportRDMAListener *info = (RDMATransportRDMAListener *)arg;
    RDMATransport *transport = info->transport;
    struct rdma_cm_event *event;
    rdma_get_cm_event(info->id->channel, &event);
    sockaddr_in *sock_addr = (sockaddr_in *)rdma_get_peer_addr(event->id);
    RDMATransportAddress addr(*sock_addr);

    switch(event->event) {
    case RDMA_CM_EVENT_CONNECT_REQUEST:
    {
        // Move the new cm into synchronous mode
        rdma_migrate_id(event->id, NULL);
        transport->ConnectRDMA(info->receiver, addr, event->id);

        // Post receive before accepting the connection
        transport->PostReceive(info);
        
        // Accept a connection
        struct rdma_conn_param params;
        params.initiator_depth = params.responder_resources = 1;
        params.rnr_retry_count = 7; /* infinite retry */
        if ((rdma_accept(event->listen_id, &params)) < 0) {
            PWarning("Failed to accept incoming RDMA connection");
            
            break;
        }
        rdma_ack_cm_event(event);
        rdma_get_cm_event(info->id->channel, &event);
        if (event->event == RDMA_CM_EVENT_ESTABLISHED) {
            Debug("Opened incoming RDMA connection from %s:%d",
                  inet_ntoa(sock_addr->sin_addr),
                  sock_addr->sin_port);
        } else {
            Warning("Could not open requested RDMA connection");
        }        
        break;
    }
    case RDMA_CM_EVENT_DISCONNECTED:
    {
        Warning("EOF on listening port");
        event_free(info->libevent);
        rdma_destroy_event_channel(info->id->channel);
        rdma_destroy_id(info->id);
        transport->rdmaOutgoing.erase(addr);
        auto it2 = transport->rdmaAddresses.find(info);
        transport->rdmaAddresses.erase(it2);
        delete info;
        break;
    }
    default:
        // ignore
        break;
    }
    rdma_ack_cm_event(event);
}

void
RDMATransport::RDMAReadableCallback(struct event *bev, void *arg)
{
    RDMATransportRDMAListener *info = (RDMATransportRDMAListener *)arg;
    RDMATransport *transport = info->transport;
    ibv_cq *cq;
    ibv_context *context;
    ibv_get_cq_event(info->channel, &cq, (void**)&context);
    
    struct ibv_wc wc;
    while (ibv_poll_cq(cq, 1, &wc) > 0) {
        if (wc.status == IBV_WC_SUCCESS) {
            switch (wc.opcode) {
            case IBV_WC_SEND:
                Debug("Done sending %s message",
                      info->sendType.c_str());
                break;
            case IBV_WC_RECV:
            {
                auto addr = transport->rdmaAddresses.find(info);
                ASSERT(addr != transport->rdmaAddresses.end());

                // Dispatch
                info->receiver->ReceiveMessage(addr->second,
                                               info->recvType,
                                               info->recvData);
                Debug("Done processing %s message",
                      info->recvType.c_str());
                break;
            }       
            default:
                // ignore
                break;
            }
                
        } else {
            Warning("Something failed!");
        }
    }
    ibv_ack_cq_events(cq, 1);
    if (ibv_req_notify_cq(cq, 0) != 0) {
        Panic("Can't set up notifications");
    }

}
