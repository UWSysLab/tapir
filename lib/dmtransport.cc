// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * dmtransport.cc:
 *   message-passing network interface that uses DM message delivery
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
#include "lib/dmtransport.h"
#include "dmtr/wait.h"
#include "lib/latency.h"

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

const size_t MAX_Dm_SIZE = 100; // XXX
const uint32_t MAGIC = 0x06121983;
static bool stopLoop = false;

static void
DmSignalCallback(int signal)
{
    ASSERT(signal == SIGTERM || signal == SIGINT);
    Warning("Set stop loop from signal");
    Latency_DumpAll();
    exit(0);
}

using std::make_pair;

DEFINE_LATENCY(process_pop);
DEFINE_LATENCY(process_push);
DEFINE_LATENCY(push_msg);
DEFINE_LATENCY(protobuf_serialize);
DEFINE_LATENCY(run_app);

DmTransportAddress::DmTransportAddress(const sockaddr_in &addr)
    : addr(addr)
{
    memset((void *)addr.sin_zero, 0, sizeof(addr.sin_zero));
}

DmTransportAddress::DmTransportAddress()
{
    memset((void *)&addr, 0, sizeof(addr));
}

DmTransportAddress *
DmTransportAddress::clone() const
{
    DmTransportAddress *c = new DmTransportAddress(*this);
    return c;    
}

bool operator==(const DmTransportAddress &a, const DmTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) == 0);
}

bool operator!=(const DmTransportAddress &a, const DmTransportAddress &b)
{
    return !(a == b);
}

bool operator<(const DmTransportAddress &a, const DmTransportAddress &b)
{
    return (memcmp(&a.addr, &b.addr, sizeof(a.addr)) < 0);
}

DmTransportAddress
DmTransport::LookupAddress(const transport::ReplicaAddress &addr)
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
        DmTransportAddress out =
            DmTransportAddress(*((sockaddr_in *)ai->ai_addr));
        freeaddrinfo(ai);
        return out;
}

DmTransportAddress
DmTransport::LookupAddress(const transport::Configuration &config,
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
    Debug("Binding to %s %d Dm", inet_ntoa(sin.sin_addr), htons(sin.sin_port));

    if (dmtr_bind(qd, (sockaddr *)&sin, sizeof(sin)) != 0) {
        PPanic("Failed to bind to socket");
    }
}

DmTransport::DmTransport(double dropRate, double reorderRate,
			   int dscp, bool handleSignals)
{
    char *argv[] = {};
    dmtr_init(0, argv);

    lastTimerId = 0;
    dmtr_queue(&timerQD);
    ASSERT(timerQD != 0);

    // Set up signal handler
    if (handleSignals) {
        struct sigaction sa;
        memset(&sa, 0, sizeof(sa));
        // Setup the sighub handler
        sa.sa_handler = &DmSignalCallback;
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
    Debug("Using Dm transport");
}

DmTransport::~DmTransport()
{
    // XXX Shut down libevent?

    //stopLoop = true;
    // for (auto kv : timers) {
    //     delete kv.second;
    // }
}

void
DmTransport::ConnectDm(TransportReceiver *src, const DmTransportAddress &dst)
{
    // Create socket
    int qd;
    if (dmtr_socket(&qd, AF_INET, SOCK_STREAM, 0) != 0) {
        PPanic("Failed to create queue for outgoing Dm connection");
    }

    //this->receiver = src;
    int res;
    if ((res = dmtr_connect(qd,
			    (struct sockaddr *)&(dst.addr),
			    sizeof(dst.addr))) != 0) {
        Panic("Failed to connect %s:%d: %s",
              inet_ntoa(dst.addr.sin_addr),
              htons(dst.addr.sin_port),
              strerror(res));
        return;
    }

    // Tell the receiver its address
    struct sockaddr_in sin;
    socklen_t sinsize = sizeof(sin);
    if (dmtr_getsockname(qd, (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    DmTransportAddress *addr = new DmTransportAddress(sin);
    src->SetAddress(addr);

    dmOutgoing.insert(make_pair(dst, qd));
    dmIncoming.insert(make_pair(qd, dst));
    receivers[qd] = src;
    
    Debug("Opened Dm connection to %s:%d",
	  inet_ntoa(dst.addr.sin_addr), htons(dst.addr.sin_port));

    dmtr_qtoken_t token;
    // add new queue to wait
    if (dmtr_pop(&token, qd) == 0)
        tokens.push_back(token);
    else
        CloseConn(qd);

}

void
DmTransport::Register(TransportReceiver *receiver,
                       const transport::Configuration &config,
                       int replicaIdx)
{
    ASSERT(replicaIdx < config.n);
    struct sockaddr_in sin;

    //const transport::Configuration *canonicalConfig =
    RegisterConfiguration(receiver, config, replicaIdx);
    this->replicaIdx = replicaIdx;
    // Clients don't need to accept Dm connections
    if (replicaIdx == -1) {
        return;
    }
    
    // Create socket
    int qd;
    if (dmtr_socket(&qd, AF_INET, SOCK_STREAM, 0) != 0) {
        PPanic("Failed to create socket to accept Dm connections");
    }
    // Registering a replica. Bind socket to the designated
    // host/port
    const string &host = config.replica(replicaIdx).host;
    const string &port = config.replica(replicaIdx).port;
    BindToPort(qd, host, port);
    
    // Listen for connections
    if (dmtr_listen(qd, 5) != 0) {
        PPanic("Failed to listen for Dm connections");
    }
        
    // Set up queue to receive connections
    this->acceptQD = qd;
    // Set up receiver to processes calls
    this->receiver = receiver;    
    
    // Tell the receiver its address
    socklen_t sinsize = sizeof(sin);
    
    if (dmtr_getsockname(qd, (sockaddr *) &sin, &sinsize) < 0) {
        PPanic("Failed to get socket name");
    }
    
    DmTransportAddress *addr = new DmTransportAddress(sin);
    receiver->SetAddress(addr);

    Debug("Accepting connections on Dm port %hu", ntohs(sin.sin_port));
}

bool
DmTransport::SendMessageInternal(TransportReceiver *src,
                                  const DmTransportAddress &dst,
                                  const Message &m,
                                  bool multicast)
{
    Latency_Start(&process_push);
    auto it = dmOutgoing.find(dst);
    // See if we have a connection open
    if (it == dmOutgoing.end()) {
        ConnectDm(src, dst);
        it = dmOutgoing.find(dst);
    }

    if (it == dmOutgoing.end()) {
        Debug("could not find connection");
        return false;
    }
    
    int qd = it->second;
    
    // Serialize message
    Latency_Start(&protobuf_serialize);
    string data = m.SerializeAsString();
    Latency_End(&protobuf_serialize);
    string type = m.GetTypeName();
    size_t typeLen = type.length();
    size_t dataLen = data.length();
    size_t totalLen = (typeLen + sizeof(typeLen) +
                       dataLen + sizeof(dataLen) +
                       sizeof(totalLen) +
                       sizeof(uint32_t));

    
    void *p = malloc(totalLen);
    assert(p != NULL);
    char *buf = reinterpret_cast<char *>(p);
    dmtr_sgarray_t sga;
    sga.sga_numsegs = 1;
    sga.sga_segs[0].sgaseg_buf = p;
    sga.sga_segs[0].sgaseg_len = totalLen;
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

    ASSERT((size_t)(ptr-buf) <= totalLen);
    ASSERT((size_t)(ptr+dataLen-buf) == totalLen);
    memcpy(ptr, data.c_str(), dataLen);
    ptr += dataLen;

    Latency_Start(&push_msg);
    dmtr_qtoken_t t;
    int ret = dmtr_push(&t, qd, &sga);
    ASSERT(ret == 0);
    ret = dmtr_wait(NULL, t);
    assert(ret == 0);
    Latency_End(&push_msg);

    Debug("Sent %ld byte %s message to server over Dm",
          totalLen, type.c_str());
    free(buf);
    Latency_End(&process_push);
    return true;
}

void
DmTransport::CloseConn(int qd)
{
    int status = dmtr_close(qd);
    dmOutgoing.erase(dmIncoming[qd]);
    dmIncoming.erase(qd);
    receivers.erase(qd);
}
    


void
DmTransport::Run()
{
    dmtr_qtoken_t token;
    int status;
    stopLoop = false;
    // check timer on clients
    if (replicaIdx == -1) {
        status = dmtr_pop(&token, timerQD);
    } else {
        // check accept on servers
        status = dmtr_accept(&token, acceptQD);
    }
    if (status != 0) {
        return;
    }
    tokens.push_back(token);
    while (!stopLoop) {
        dmtr_qresult wait_out;
        int ready_idx;
        int status = dmtr_wait_any(&wait_out, &ready_idx, tokens.data(), tokens.size());

        // if we got an EOK back from wait
        if (status == 0) {
            Debug("Found something: qd=%lx",
                  wait_out.qr_qd);
            // check timer on clients
            if (replicaIdx == -1 && wait_out.qr_qd == timerQD) {
		dmtr_sgarray_t &sga = wait_out.qr_value.sga;
                assert(sga.sga_numsegs == 1);
                OnTimer(reinterpret_cast<DmTransportTimerInfo *>(sga.sga_buf));
                status = dmtr_pop(&token, timerQD);
            } else if (wait_out.qr_qd == acceptQD) {
                // check accept on servers
                DmAcceptCallback(wait_out.qr_value.ares);
                // call accept again
                status = dmtr_accept(&token, acceptQD);
            } else {
                // process request
		dmtr_sgarray_t &sga = wait_out.qr_value.sga;
                assert(sga.sga_numsegs > 0);
                DmPopCallback(wait_out.qr_qd, receivers[wait_out.qr_qd], sga);
		status = dmtr_pop(&token, wait_out.qr_qd);
            }
        } // else fall through, typically connection closed
	
        if (status == 0)
            tokens[ready_idx] = token;
        else {
            if (wait_out.qr_qd == acceptQD || wait_out.qr_qd == timerQD)
                break;
            //assert(status == ECONNRESET || status == ECONNABORTED);
            CloseConn(wait_out.qr_qd);
            tokens.erase(tokens.begin()+ready_idx);
        }
    }
    Warning("Exited loop");
    Latency_DumpAll();
}

void
DmTransport::Stop()
{
    for (auto &it : receivers) {
        int qd = it.first;
        CloseConn(qd);
    }
    Warning("Stop loop  was called");
    stopLoop = true;
}

int
DmTransport::Timer(uint64_t ms, timer_callback_t cb)
{
    if (ms == 0) {
        DmTransportTimerInfo *info = new DmTransportTimerInfo();
        ++lastTimerId;
        
        info->id = lastTimerId;
        info->cb = cb;
    
        timers[info->id] = info;
        
        dmtr_sgarray_t sga = {};
	sga.sga_buf = reinterpret_cast<void *>(info);
        sga.sga_numsegs = 1;
	sga.sga_segs[0].sgaseg_buf = reinterpret_cast<void *>(info);
	sga.sga_segs[0].sgaseg_len = sizeof(DmTransportTimerInfo);
        dmtr_qtoken_t qt;
        int ret = dmtr_push(&qt, timerQD, &sga);
	assert(ret == 0);
	ret = dmtr_wait(NULL, qt);
	assert(ret == 0);
	return info->id;
    }
    return 0;
}

bool
DmTransport::CancelTimer(int id)
{
    DmTransportTimerInfo *info = timers[id];

    if (info == NULL) {
        return false;
    }

    timers.erase(info->id);
    delete info;
    
    return true;
}

void
DmTransport::CancelAllTimers()
{
    while (!timers.empty()) {
        auto kv = timers.begin();
        CancelTimer(kv->first);
    }
}

void
DmTransport::OnTimer(DmTransportTimerInfo *info)
{
    timers.erase(info->id);
    info->cb();
    delete info;
}

void
DmTransport::DmAcceptCallback(dmtr_accept_result ares)
{
    int newqd = ares.qd;
    dmtr_qtoken_t token;
    DmTransportAddress client = DmTransportAddress(ares.addr); 
    dmOutgoing[client] = newqd;
    dmIncoming.insert(std::pair<int, DmTransportAddress>(newqd,client));
    receivers[newqd] = receiver;
 
    // add new queue to wait
    if (dmtr_pop(&token, newqd) == 0) {
        tokens.push_back(token);
    
        Debug("Opened incoming Dm connection from %s:%d",
              inet_ntoa(ares.addr.sin_addr), htons(ares.addr.sin_port));
    } else {
        CloseConn(newqd);
    }
}

void
DmTransport::DmPopCallback(int qd,
                           TransportReceiver *receiver,
                           dmtr_sgarray_t &sga)
    
{
    Debug("Pop Callback");

    
    Latency_Start(&process_pop);
    auto addr = dmIncoming.find(qd);
    
    ASSERT(sga.sga_numsegs == 1);
    uint8_t *ptr = (uint8_t *)sga.sga_segs[0].sgaseg_buf;
    ASSERT(sga.sga_segs[0].sgaseg_len > 0);
    uint32_t magic = *(uint32_t *)ptr;
    Debug("[%x] MAGIC=%x", qd, magic);
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
    Latency_Start(&run_app);
    receiver->ReceiveMessage(addr->second,
                             type,
                             data);
    Latency_End(&run_app);
    free(sga.sga_buf);
    Latency_End(&process_pop);

    Debug("Done processing large %s message", type.c_str());        
}
