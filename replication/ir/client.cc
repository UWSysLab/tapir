  // -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
  /***********************************************************************
 *
 * ir/client.cc:
 *   Inconsistent replication client
 *
 * Copyright 2013-2015 Dan R. K. Ports  <drkp@cs.washington.edu>
 *                     Irene Zhang Ports  <iyzhang@cs.washington.edu>
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
      lastReqId(0)
{
    
}

IRClient::~IRClient()
{
    for (auto kv : pendingReqs) {
	delete kv.second;
    }
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
    // Bump the request ID
    uint64_t reqId = ++lastReqId;
    // Create new timer
    Timeout *timer = new Timeout(transport, 500, [this, reqId]() {
            ResendInconsistent(reqId);
        });
    PendingInconsistentRequest *req =
	new PendingInconsistentRequest(request,
                                   reqId,
                                   continuation,
                                   timer,
                                   config.QuorumSize());
    pendingReqs[reqId] = req;
    SendInconsistent(req);
}
void
IRClient::SendInconsistent(const PendingInconsistentRequest *req)
{
    
    proto::ProposeInconsistentMessage reqMsg;
    reqMsg.mutable_req()->set_op(req->request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(req->clientReqId);
     
    if (transport->SendMessageToAll(this, reqMsg)) {   
        req->timer->Reset();
    } else {
        Warning("Could not send inconsistent request to replicas");
        pendingReqs.erase(req->clientReqId);
        delete req;
    }
}
    
void
IRClient::InvokeConsensus(const string &request,
                          decide_t decide,
                          continuation_t continuation)
{
    uint64_t reqId = ++lastReqId;
    Timeout *timer = new Timeout(transport, 500, [this, reqId]() {
            ConsensusSlowPath(reqId);
        });
    
    PendingConsensusRequest *req =
	new PendingConsensusRequest(request,
				    reqId,
				    continuation,
				    timer,
				    config.QuorumSize(),
				    config.QuorumSize() + ceil(0.5 * config.QuorumSize()),
				    decide);
    
    proto::ProposeConsensusMessage reqMsg;
    reqMsg.mutable_req()->set_op(request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(reqId);

    if (transport->SendMessageToAll(this, reqMsg)) {
        req->timer->Start();
	pendingReqs[reqId] = req;
    } else {
        Warning("Could not send consensus request to replicas");
	delete req;
    }
}

void
IRClient::InvokeUnlogged(int replicaIdx,
                         const string &request,
                         continuation_t continuation,
                         timeout_continuation_t timeoutContinuation,
                         uint32_t timeout)
{
    uint64_t reqId = ++lastReqId;
    Timeout *timer =
	new Timeout(transport, timeout, [this, reqId]() {
            UnloggedRequestTimeoutCallback(reqId);
        });

    PendingUnloggedRequest *req =
	new PendingUnloggedRequest(request,
				   reqId,
				   continuation,
				   timeoutContinuation,
				   timer);

    proto::UnloggedRequestMessage reqMsg;
    reqMsg.mutable_req()->set_op(request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(reqId);

    if (transport->SendMessageToReplica(this, replicaIdx, reqMsg)) {
	req->timer->Start();
	pendingReqs[reqId] = req;
    } else {
        Warning("Could not send unlogged request to replica");
	delete req;
    }
}

void
IRClient::ResendInconsistent(const uint64_t reqId)
{
    
    Warning("Client timeout; resending inconsistent request: %lu", reqId);
    SendInconsistent((PendingInconsistentRequest *)pendingReqs[reqId]);
}

void
IRClient::ConsensusSlowPath(const uint64_t reqId)
{
    PendingConsensusRequest *req = static_cast<PendingConsensusRequest *>(pendingReqs[reqId]);
    // Make sure the dynamic cast worked
    ASSERT(req != NULL);

    // Give up on the fast path 
    req->timer->Stop();
    delete req->timer;
    // set up a new timer for the slow path
    req->timer = new Timeout(transport, 500, [this, reqId]() {
            ResendConfirmation(reqId, true);
        });

	
    Debug("Client timeout; taking consensus slow path: %lu", reqId);

    // get results so far
    viewstamp_t vs = { view, reqId };
    auto msgs = req->consensusReplyQuorum.GetMessages(vs);

    // construct result set
    set<string> results;
    for (auto &msg : msgs) {
        results.insert(msg.second.result());
    }

    // Upcall into the application
    ASSERT(req->decide != NULL);
    string result = req->decide(results);

    // Put the result in the request to store for later retries
    req->decideResult = result;

    // Send finalize message
    proto::FinalizeConsensusMessage response;
    response.mutable_opid()->set_clientid(clientid);
    response.mutable_opid()->set_clientreqid(req->clientReqId);
    response.set_result(result);
                
    if(transport->SendMessageToAll(this, response)) {
        req->timer->Start();
    } else {
        Warning("Could not send finalize message to replicas");
	pendingReqs.erase(reqId);
	delete req;
    }
}

void
IRClient::ResendConfirmation(const uint64_t reqId, bool isConsensus)
{
    if (pendingReqs.find(reqId) == pendingReqs.end()) {
        Debug("Received resend request when no request was pending");
        return;
    }

    if (isConsensus) {
	PendingConsensusRequest *req = static_cast<PendingConsensusRequest *>(pendingReqs[reqId]);
	ASSERT(req != NULL);
	
        proto::FinalizeConsensusMessage response;
        response.mutable_opid()->set_clientid(clientid);
        response.mutable_opid()->set_clientreqid(req->clientReqId);
        response.set_result(req->decideResult);
                 
        if(transport->SendMessageToAll(this, response)) {
            req->timer->Reset();
        } else {
            Warning("Could not send finalize message to replicas");
	    // give up and clean up
	    pendingReqs.erase(reqId);
	    delete req;
        }
    } else {
	PendingInconsistentRequest *req = static_cast<PendingInconsistentRequest *>(pendingReqs[reqId]);
	ASSERT(req != NULL);

	proto::FinalizeInconsistentMessage response;
        response.mutable_opid()->set_clientid(clientid);
        response.mutable_opid()->set_clientreqid(req->clientReqId);

        if (transport->SendMessageToAll(this, response)) {
	    req->timer->Reset();
	} else {
            Warning("Could not send finalize message to replicas");
	    pendingReqs.erase(reqId);
	    delete req;
        } 

    }
	
}

void
IRClient::ReceiveMessage(const TransportAddress &remote,
                         const string &type,
                         const string &data)
{
    proto::ReplyInconsistentMessage replyInconsistent;
    proto::ReplyConsensusMessage replyConsensus;
    proto::ConfirmMessage confirm;
    proto::UnloggedReplyMessage unloggedReply;
    
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
    uint64_t reqId = msg.opid().clientreqid();
    auto it = pendingReqs.find(reqId);
    if (it == pendingReqs.end()) {
        Debug("Received reply when no request was pending");
        return;
    }

    PendingInconsistentRequest *req =
        static_cast<PendingInconsistentRequest *>(it->second);
    // Make sure the dynamic cast worked
    ASSERT(req != NULL);
    
    Debug("Client received reply: %lu %i", reqId,
          req->inconsistentReplyQuorum.NumRequired());

    // Record replies
    viewstamp_t vs = { msg.view(), reqId };
    if (req->inconsistentReplyQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg)) {
        // If all quorum received, then send finalize and return to client
        // Return to client
        if (!req->continuationInvoked) {
            req->timer->Stop();
            delete req->timer;
            req->timer = new Timeout(transport, 500, [this, reqId]() {
                    ResendConfirmation(reqId, false);
                });

            // asynchronously send the finalize message
            proto::FinalizeInconsistentMessage response;
            *(response.mutable_opid()) = msg.opid();

            if (transport->SendMessageToAll(this, response)) {
                req->timer->Start();
            } else {
                Warning("Could not send finalize message to replicas");
            } 

            req->continuation(req->request, "");
            req->continuationInvoked = true;       
        }
    }
}

void
IRClient::HandleConsensusReply(const TransportAddress &remote,
                               const proto::ReplyConsensusMessage &msg)
{
    uint64_t reqId = msg.opid().clientreqid();
    auto it = pendingReqs.find(reqId); 
    if (it == pendingReqs.end()) {
        Debug("Received reply when no request was pending");
        return;
    }
    PendingConsensusRequest *req = static_cast<PendingConsensusRequest *>(it->second);
   
    Debug("Client received reply: %lu %i", reqId, req->consensusReplyQuorum.NumRequired());

    // Record replies
    viewstamp_t vs = { msg.view(), reqId };
    if (auto msgs =
        (req->consensusReplyQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg))) {
        // If all quorum received, then check return values

        map<string, int> results;
        // count matching results
        for (auto &m : *msgs) {
            if (results.count(m.second.result()) > 0) {
                results[m.second.result()] = results[m.second.result()] + 1;
            } else {
                results[m.second.result()] = 1;
            }
        }

        // Check that there are a quorum of *matching* results
        for (auto result : results) {
            if (result.second >= req->consensusReplyQuorum.NumRequired()) {
                req->timer->Stop();
                delete req->timer;
                // set up new timeout for finalize phase
                req->timer =
                    new Timeout(transport, 500, [this, reqId]() {
                            ResendConfirmation(reqId, true);
                            });

                // asynchronously send the finalize message
                proto::FinalizeConsensusMessage response;
                *response.mutable_opid() = msg.opid();
                response.set_result(result.first);

                req->decideResult = result.first;

                if(transport->SendMessageToAll(this, response)) {
                    // Start the timer
                    req->timer->Start();
                } else {
                    Warning("Could not send finalize message to replicas");
                    // give up and clean up
                    pendingReqs.erase(it);
                    delete req;
                }

                // Return to client
                if (!req->continuationInvoked) {
                    req->continuation(req->request, result.first);
                    req->continuationInvoked = true;
                }
                break;
            }
        }
    }
}

void
IRClient::HandleConfirm(const TransportAddress &remote,
                        const proto::ConfirmMessage &msg)
{
    uint64_t reqId = msg.opid().clientreqid();
    auto it = pendingReqs.find(reqId); 
    if (it == pendingReqs.end()) {
        // ignore, we weren't waiting for the confirmation
        return;
    }

    PendingRequest *req = it->second;
    
    viewstamp_t vs = { msg.view(), reqId };
    if (req->confirmQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg)) {
        req->timer->Stop();
        pendingReqs.erase(it);
        if (!req->continuationInvoked) {
            // Return to client
            PendingConsensusRequest *r2 = static_cast<PendingConsensusRequest *>(req);
            r2->continuation(r2->request, r2->decideResult);
        }
        delete req;
    }
}

void
IRClient::HandleUnloggedReply(const TransportAddress &remote,
                              const proto::UnloggedReplyMessage &msg)
{
    uint64_t reqId = msg.clientreqid();
    auto it = pendingReqs.find(reqId); 
    if (it == pendingReqs.end()) {
        Debug("Received reply when no request was pending");
        return;
    }

    PendingRequest *req = it->second;
    // delete timer event
    req->timer->Stop();
    // remove from pending list
    pendingReqs.erase(it);
    // invoke application callback
    req->continuation(req->request, msg.reply());
    delete req;
}

void
IRClient::UnloggedRequestTimeoutCallback(const uint64_t reqId)
{
    auto it = pendingReqs.find(reqId);
    if (it == pendingReqs.end()) {
        Debug("Received timeout when no request was pending");
        return;
    }

    PendingUnloggedRequest *req = static_cast<PendingUnloggedRequest *>(it->second);
    ASSERT(req != NULL);

    Warning("Unlogged request timed out");
    // delete timer event
    req->timer->Stop();
    // remove from pending list
    pendingReqs.erase(it);
    // invoke application callback
    req->timeoutContinuation(req->request);
    delete req;
}

} // namespace ir
} // namespace replication
