  // -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
  /***********************************************************************
 *
 * ir/client.cc:
 *   Inconsistent replication client
 *
 * Copyright 2013-2015 Dan R. K. Ports  <drkp@cs.washington.edu>
 *                     Irene Zhang Ports  <iyzhang@cs.washington.edu>
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

#include "replication/common/client.h"
#include "replication/common/request.pb.h"
#include "lib/assert.h"
#include "lib/message.h"
#include "lib/transport.h"
#include "replication/ir/client.h"
#include "replication/ir/ir-proto.pb.h"

#include <math.h>

namespace replication {
namespace ir {

using namespace std;

IRClient::IRClient(const transport::Configuration &config,
                   Transport *transport,
                   uint64_t clientid)
    : Client(config, transport, clientid),
      view(0),
      lastReqId(0),
      inconsistentReplyQuorum(config.QuorumSize()-1),
      consensusReplyQuorum(config.QuorumSize() + ceil(0.5 * config.QuorumSize()) -1),
      confirmQuorum(config.QuorumSize()-1)
{
    pendingInconsistentRequest = NULL;
    pendingConsensusRequest = NULL;
    pendingUnloggedRequest = NULL;
    
    inconsistentRequestTimeout = new Timeout(transport, 500, [this]() {
            ResendInconsistent();
        });
    consensusRequestTimeout = new Timeout(transport, 500, [this]() {
            ConsensusSlowPath();
        });
    confirmationTimeout = new Timeout(transport, 500, [this]() {
            ResendConfirmation();
        });
    unloggedRequestTimeout = new Timeout(transport, 500, [this]() {
            UnloggedRequestTimeoutCallback();
        });
}

IRClient::~IRClient()
{
    if (pendingInconsistentRequest) {
        delete pendingInconsistentRequest;
    }

    if (pendingInconsistentRequest) {
        delete pendingConsensusRequest;
    }

    if (pendingUnloggedRequest) {
        delete pendingUnloggedRequest;
    }
    delete inconsistentRequestTimeout;
    delete consensusRequestTimeout;
    delete confirmationTimeout;
    delete unloggedRequestTimeout;
}

void
IRClient::Invoke(const string &request,
                 continuation_t continuation)
{
    InvokeInconsistent(request, continuation);
}

void
IRClient::InvokeInconsistent(const string &request,
                             continuation_t continuation)
{
    // XXX Can only handle one pending request for now
    if (pendingInconsistentRequest != NULL) {
        Panic("Client only supports one pending request");
    }

    ++lastReqId;
    uint64_t reqId = lastReqId;
    pendingInconsistentRequest = new PendingRequest(request, reqId, continuation);

    SendInconsistent();
}

void
IRClient::SendInconsistent()
{
    ASSERT(pendingInconsistentRequest != NULL);
    
    proto::ProposeInconsistentMessage reqMsg;
    reqMsg.mutable_req()->set_op(pendingInconsistentRequest->request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(pendingInconsistentRequest->clientReqId);
    
    if (transport->SendMessageToAll(this, reqMsg)) {   
        inconsistentRequestTimeout->Reset();
    } else {
        Warning("Could not send inconsistent request to replicas");
    }
}
    
void
IRClient::InvokeConsensus(const string &request,
                          decide_t decide,
                          continuation_t continuation)
{
    // XXX Can only handle one pending request for now
    if (pendingConsensusRequest != NULL) {
        Panic("Client only supports one pending request");
    }

    ++lastReqId;
    uint64_t reqId = lastReqId;
    
    pendingConsensusRequest = new PendingRequest(request, reqId, continuation);
    pendingConsensusRequest->decide = decide;
    
    proto::ProposeConsensusMessage reqMsg;
    reqMsg.mutable_req()->set_op(pendingConsensusRequest->request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(pendingConsensusRequest->clientReqId);

    if (transport->SendMessageToAll(this, reqMsg)) {
        consensusRequestTimeout->Reset();
    } else {
        Warning("Could not send consensus request to replicas");
    }
}

void
IRClient::InvokeUnlogged(int replicaIdx,
                         const string &request,
                         continuation_t continuation,
                         timeout_continuation_t timeoutContinuation,
                         uint32_t timeout)
{
    // XXX Can only handle one pending request for now
    if (pendingUnloggedRequest != NULL) {
        Panic("Client only supports one pending unlogged request");
    }

    ++lastReqId;
    uint64_t reqId = lastReqId;

    pendingUnloggedRequest = new PendingRequest(request, reqId, continuation);
    pendingUnloggedRequest->timeoutContinuation = timeoutContinuation;

    proto::UnloggedRequestMessage reqMsg;
    reqMsg.mutable_req()->set_op(pendingUnloggedRequest->request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(pendingUnloggedRequest->clientReqId);

    ASSERT(!unloggedRequestTimeout->Active());

    if (transport->SendMessageToReplica(this, replicaIdx, reqMsg)) {
        unloggedRequestTimeout->SetTimeout(timeout);
        unloggedRequestTimeout->Start();
    } else {
        Warning("Could not send unlogged request to replica");
    }
}

void
IRClient::ResendInconsistent()
{
    if (pendingInconsistentRequest == NULL) {
        inconsistentRequestTimeout->Stop();
        return;
    }
    
    Warning("Client timeout; resending inconsistent request: %lu", pendingInconsistentRequest->clientReqId);
    SendInconsistent();
}

void
IRClient::ConsensusSlowPath()
{
    // Give up on the fast path 
    consensusRequestTimeout->Stop();
    
    if (pendingConsensusRequest == NULL) {
        Warning("No consensus operation pending");
        return;
    }

    Notice("Client timeout; taking consensus slow path: %lu", pendingConsensusRequest->clientReqId);

    // get results so far
    viewstamp_t vs = { view, pendingConsensusRequest->clientReqId };
    auto msgs = consensusReplyQuorum.GetMessages(vs);

    // construct result set
    set<string> results;
    for (auto &msg : msgs) {
        results.insert(msg.second.result());
    }

    // Upcall into the application
    ASSERT(pendingConsensusRequest->decide != NULL);
    string result = pendingConsensusRequest->decide(results);

    // Put the result in the request to store for later retries
    pendingConsensusRequest->request = result;

    // Send finalize message
    proto::FinalizeConsensusMessage response;
    response.mutable_opid()->set_clientid(clientid);
    response.mutable_opid()->set_clientreqid(pendingConsensusRequest->clientReqId);
    response.set_result(result);
                
    if(transport->SendMessageToAll(this, response)) {
        confirmationTimeout->Reset();
    } else {
        Warning("Could not send finalize message to replicas");
    }
}

void
IRClient::ResendConfirmation()
{
    if (pendingConsensusRequest == NULL) {
        // Unless we are waiting for a confirm to finish up a
        // consensus slow path, just ignore
        confirmationTimeout->Stop();
    } else {
        proto::FinalizeConsensusMessage response;
        response.mutable_opid()->set_clientid(clientid);
        response.mutable_opid()->set_clientreqid(pendingConsensusRequest->clientReqId);
        response.set_result(pendingConsensusRequest->request);
                 
        if(transport->SendMessageToAll(this, response)) {
            confirmationTimeout->Reset();
        } else {
            Warning("Could not send finalize message to replicas");
        }
    }
}

void
IRClient::ReceiveMessage(const TransportAddress &remote,
                         const string &type,
                         const string &data)
{
    static proto::ReplyInconsistentMessage replyInconsistent;
    static proto::ReplyConsensusMessage replyConsensus;
    static proto::ConfirmMessage confirm;
    static proto::UnloggedReplyMessage unloggedReply;
    
    if (type == replyInconsistent.GetTypeName()) {
        replyInconsistent.ParseFromString(data);
        HandleInconsistentReply(remote, replyInconsistent);
    } else if (type == replyConsensus.GetTypeName()) {
        replyConsensus.ParseFromString(data);
        HandleConsensusReply(remote, replyConsensus);
    } else if (type == confirm.GetTypeName()) {
        confirm.ParseFromString(data);
        HandleConfirm(remote, confirm);
    } else if (type == unloggedReply.GetTypeName()) {
        unloggedReply.ParseFromString(data);
        HandleUnloggedReply(remote, unloggedReply);
    } else {
        Client::ReceiveMessage(remote, type, data);
    }
}

void
IRClient::HandleInconsistentReply(const TransportAddress &remote,
                                  const proto::ReplyInconsistentMessage &msg)
{
    if (pendingInconsistentRequest == NULL) {
        Warning("Received reply when no request was pending");
        return;
    }
    
    if (msg.opid().clientreqid() != pendingInconsistentRequest->clientReqId) {
        Debug("Received reply for a different request");
        return;
    }

    
    Debug("Client received reply: %lu", pendingInconsistentRequest->clientReqId);

    // Record replies
    viewstamp_t vs = { msg.view(), msg.opid().clientreqid() };
    if (inconsistentReplyQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg)) {
        // If all quorum received, then send finalize and return to client

        inconsistentRequestTimeout->Stop();

        PendingRequest *req = pendingInconsistentRequest;
        pendingInconsistentRequest = NULL;

        // asynchronously send the finalize message
        proto::FinalizeInconsistentMessage response;
        *(response.mutable_opid()) = msg.opid();

        if (!transport->SendMessageToAll(this, response)) {
            Warning("Could not send finalize message to replicas");
        } // don't use the confirmation timeout for async replies

        // Return to client
        req->continuation(req->request, "");
        delete req;
    }
}

void
IRClient::HandleConsensusReply(const TransportAddress &remote,
                               const proto::ReplyConsensusMessage &msg)
{
    if (pendingConsensusRequest == NULL) {
        Warning("Received reply when no request was pending");
        return;
    }
    
    if (msg.opid().clientreqid() != pendingConsensusRequest->clientReqId) {
        Debug("Received reply for a different request");
        return;
    }

    
    Debug("Client received reply: %lu", pendingConsensusRequest->clientReqId);

    // Record replies
    viewstamp_t vs = { msg.view(), msg.opid().clientreqid() };
    if (auto msgs =
        (consensusReplyQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg))) {
        // If all quorum received, then check return values

        map<string, int> results;
        // count matching results
        for (auto &m : *msgs) {
            results[m.second.result()] = results.count(m.second.result()) + 1;
        }

        // Check that there are a quorum of *matching* results
        for (auto result : results) {
            if (result.second >= consensusReplyQuorum.NumRequired()) {
                consensusRequestTimeout->Stop();

                PendingRequest *req = pendingConsensusRequest;
                pendingConsensusRequest = NULL;

                // asynchronously send the finalize message
                proto::FinalizeConsensusMessage response;
                *response.mutable_opid() = msg.opid();
                response.set_result(result.first);
                
                if(!transport->SendMessageToAll(this, response)) {
                    Warning("Could not send finalize message to replicas");
                } // don't reset the confirm timeout on fast path

                // Return to client
                req->continuation(req->request, result.first);
                delete req;
                break;
            }
        }
    }
}

void
IRClient::HandleConfirm(const TransportAddress &remote,
                        const proto::ConfirmMessage &msg)
{
    if (pendingConsensusRequest == NULL) {
        // if no pending request, then we were waiting for a synchronous confirmation
        return;
    }
    
    if (msg.opid().clientreqid() != pendingConsensusRequest->clientReqId) {
        Debug("Received reply for a different request");
        return;
    }

    // otherwise, we are waiting on a finalized consensus result
    // Record replies
    viewstamp_t vs = { msg.view(), msg.opid().clientreqid() };
    if (confirmQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg)) {
        confirmationTimeout->Stop();

        PendingRequest *req = pendingConsensusRequest;
        pendingConsensusRequest = NULL;

        // Return to client
        req->continuation(req->request, pendingConsensusRequest->request);
        delete req;
    }
}

void
IRClient::HandleUnloggedReply(const TransportAddress &remote,
                              const proto::UnloggedReplyMessage &msg)
{
    if (pendingUnloggedRequest == NULL) {
        Warning("Received unloggedReply when no request was pending");
        return;
    }
    
    Debug("Client received unloggedReply");

    unloggedRequestTimeout->Stop();

    PendingRequest *req = pendingUnloggedRequest;
    pendingUnloggedRequest = NULL;
    
    req->continuation(req->request, msg.reply());
    delete req;
}

void
IRClient::UnloggedRequestTimeoutCallback()
{
    PendingRequest *req = pendingUnloggedRequest;
    pendingUnloggedRequest = NULL;

    Warning("Unlogged request timed out");

    unloggedRequestTimeout->Stop();
    
    req->timeoutContinuation(req->request);
}

} // namespace ir
} // namespace replication
