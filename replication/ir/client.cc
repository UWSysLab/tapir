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
                 continuation_t continuation,
                 error_continuation_t error_continuation)
{
    InvokeInconsistent(request, continuation, error_continuation);
}

void
IRClient::InvokeInconsistent(const string &request,
                             continuation_t continuation,
                             error_continuation_t error_continuation)
{
    // TODO: Use error_continuation.
    (void) error_continuation;

    // Bump the request ID
    uint64_t reqId = ++lastReqId;
    // Create new timer
    auto timer = std::unique_ptr<Timeout>(new Timeout(
        transport, 500, [this, reqId]() { ResendInconsistent(reqId); }));
    PendingInconsistentRequest *req =
	new PendingInconsistentRequest(request,
                                   reqId,
                                   continuation,
                                   std::move(timer),
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
                          continuation_t continuation,
                          error_continuation_t error_continuation)
{
    uint64_t reqId = ++lastReqId;
    auto timer = std::unique_ptr<Timeout>(new Timeout(
        transport, 500, [this, reqId]() { ResendConsensus(reqId); }));
    auto transition_to_slow_path_timer =
        std::unique_ptr<Timeout>(new Timeout(transport, 500, [this, reqId]() {
            TransitionToConsensusSlowPath(reqId);
        }));

    PendingConsensusRequest *req =
	new PendingConsensusRequest(request,
				    reqId,
				    continuation,
				    std::move(timer),
				    std::move(transition_to_slow_path_timer),
				    config.QuorumSize(),
				    config.FastQuorumSize(),
				    decide,
                    error_continuation);

    proto::ProposeConsensusMessage reqMsg;
    reqMsg.mutable_req()->set_op(request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(reqId);

	pendingReqs[reqId] = req;
    req->transition_to_slow_path_timer->Start();
    SendConsensus(req);
}

void
IRClient::SendConsensus(const PendingConsensusRequest *req)
{
    proto::ProposeConsensusMessage reqMsg;
    reqMsg.mutable_req()->set_op(req->request);
    reqMsg.mutable_req()->set_clientid(clientid);
    reqMsg.mutable_req()->set_clientreqid(req->clientReqId);

    if (transport->SendMessageToAll(this, reqMsg)) {
        req->timer->Reset();
    } else {
        Warning("Could not send consensus request to replicas");
        pendingReqs.erase(req->clientReqId);
        delete req;
    }
}

void
IRClient::InvokeUnlogged(int replicaIdx,
                         const string &request,
                         continuation_t continuation,
                         error_continuation_t error_continuation,
                         uint32_t timeout)
{
    uint64_t reqId = ++lastReqId;
    auto timer = std::unique_ptr<Timeout>(new Timeout(
        transport, timeout,
        [this, reqId]() { UnloggedRequestTimeoutCallback(reqId); }));

    PendingUnloggedRequest *req =
	new PendingUnloggedRequest(request,
				   reqId,
				   continuation,
				   error_continuation,
				   std::move(timer));

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
IRClient::ResendConsensus(const uint64_t reqId)
{

    Warning("Client timeout; resending consensus request: %lu", reqId);
    SendConsensus((PendingConsensusRequest *)pendingReqs[reqId]);
}

void
IRClient::TransitionToConsensusSlowPath(const uint64_t reqId)
{
    Debug("Client timeout; taking consensus slow path: reqId=%lu", reqId);
    PendingConsensusRequest *req =
        dynamic_cast<PendingConsensusRequest *>(pendingReqs[reqId]);
    ASSERT(req != NULL);
    req->on_slow_path = true;

    // We've already transitioned into the slow path, so don't transition into
    // the slow-path again.
    ASSERT(req->transition_to_slow_path_timer);
    req->transition_to_slow_path_timer.reset();

    // It's possible that we already have a quorum of responses (but not a
    // super quorum).
    const std::map<int, proto::ReplyConsensusMessage> *quorum =
        req->consensusReplyQuorum.CheckForQuorum();
    if (quorum != nullptr) {
        HandleSlowPathConsensus(reqId, *quorum, false, req);
    }
}

void IRClient::HandleSlowPathConsensus(
    const uint64_t reqid,
    const std::map<int, proto::ReplyConsensusMessage> &msgs,
    const bool finalized_result_found,
    PendingConsensusRequest *req)
{
    ASSERT(finalized_result_found || msgs.size() >= req->quorumSize);
    Debug("Handling slow path for request %lu.", reqid);

    // If a finalized result wasn't found, call decide to determine the
    // finalized result.
    if (!finalized_result_found) {
        uint64_t view = 0;
        std::map<string, std::size_t> results;
        for (const auto &p : msgs) {
            const proto::ReplyConsensusMessage &msg = p.second;
            results[msg.result()] += 1;

            // All messages should have the same view.
            if (view == 0) {
                view = msg.view();
            }
            ASSERT(msg.view() == view);
        }

        // Upcall into the application, and put the result in the request
        // to store for later retries.
        ASSERT(req->decide != NULL);
        req->decideResult = req->decide(results);
        req->reply_consensus_view = view;
    }

    // Set up a new timer for the finalize phase.
    req->timer = std::unique_ptr<Timeout>(
        new Timeout(transport, 500, [this, reqid]() {  //
            ResendConfirmation(reqid, true);
        }));

    // Send finalize message.
    proto::FinalizeConsensusMessage response;
    response.mutable_opid()->set_clientid(clientid);
    response.mutable_opid()->set_clientreqid(reqid);
    response.set_result(req->decideResult);
    if (transport->SendMessageToAll(this, response)) {
        Debug("FinalizeConsensusMessages sent for request %lu.", reqid);
        req->sent_confirms = true;
        req->timer->Start();
    } else {
        Warning("Could not send finalize message to replicas");
        pendingReqs.erase(reqid);
        delete req;
    }
}

void IRClient::HandleFastPathConsensus(
    const uint64_t reqid,
    const std::map<int, proto::ReplyConsensusMessage> &msgs,
    PendingConsensusRequest *req)
{
    ASSERT(msgs.size() >= req->superQuorumSize);
    Debug("Handling fast path for request %lu.", reqid);

    // We've received a super quorum of responses. Now, we have to check to see
    // if we have a super quorum of _matching_ responses.
    map<string, std::size_t> results;
    for (const auto &m : msgs) {
        const std::string &result = m.second.result();
        results[result]++;
    }

    for (const auto &result : results) {
        if (result.second < req->superQuorumSize) {
            continue;
        }

        // A super quorum of matching requests was found!
        Debug("A super quorum of matching requests was found for request %lu.",
              reqid);
        req->decideResult = result.first;

        // Set up a new timeout for the finalize phase.
        req->timer = std::unique_ptr<Timeout>(new Timeout(
            transport, 500,
            [this, reqid]() { ResendConfirmation(reqid, true); }));

        // Asynchronously send the finalize message.
        proto::FinalizeConsensusMessage response;
        response.mutable_opid()->set_clientid(clientid);
        response.mutable_opid()->set_clientreqid(reqid);
        response.set_result(result.first);
        if (transport->SendMessageToAll(this, response)) {
            Debug("FinalizeConsensusMessages sent for request %lu.", reqid);
            req->sent_confirms = true;
            req->timer->Start();
        } else {
            Warning("Could not send finalize message to replicas");
            pendingReqs.erase(reqid);
            delete req;
        }

        // Return to the client.
        if (!req->continuationInvoked) {
            req->continuation(req->request, req->decideResult);
            req->continuationInvoked = true;
        }
        return;
    }

    // There was not a super quorum of matching results, so we transition into
    // the slow path.
    Debug("A super quorum of matching requests was NOT found for request %lu.",
          reqid);
    req->on_slow_path = true;
    if (req->transition_to_slow_path_timer) {
        req->transition_to_slow_path_timer.reset();
    }
    HandleSlowPathConsensus(reqid, msgs, false, req);
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
        dynamic_cast<PendingInconsistentRequest *>(it->second);
    // Make sure the dynamic cast worked
    ASSERT(req != NULL);

    Debug("Client received reply: %lu %i", reqId,
          req->inconsistentReplyQuorum.NumRequired());

    // Record replies
    viewstamp_t vs = { msg.view(), reqId };
    if (req->inconsistentReplyQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg)) {
        // TODO: Some of the ReplyInconsistentMessages might already be
        // finalized. If this is the case, then we don't have to send finalize
        // messages to them. It's not incorrect to send them anyway (which this
        // code does) but it's less efficient.

        // If all quorum received, then send finalize and return to client
        // Return to client
        if (!req->continuationInvoked) {
            req->timer = std::unique_ptr<Timeout>(new Timeout(
                transport, 500,
                [this, reqId]() { ResendConfirmation(reqId, false); }));

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
    Debug(
        "Client received ReplyConsensusMessage from replica %i in view %lu for "
        "request %lu.",
        msg.replicaidx(), msg.view(), reqId);

    auto it = pendingReqs.find(reqId);
    if (it == pendingReqs.end()) {
        Debug(
            "Client was not expecting a ReplyConsensusMessage for request %lu, "
            "so it is ignoring the request.",
            reqId);
        return;
    }

    PendingConsensusRequest *req =
        dynamic_cast<PendingConsensusRequest *>(it->second);
    ASSERT(req != nullptr);

    if (req->sent_confirms) {
        Debug(
            "Client has already received a quorum or super quorum of "
            "HandleConsensusReply for request %lu and has already sent out "
            "ConfirmMessages.",
            reqId);
        return;
    }

    req->consensusReplyQuorum.Add(msg.view(), msg.replicaidx(), msg);
    const std::map<int, proto::ReplyConsensusMessage> &msgs =
        req->consensusReplyQuorum.GetMessages(msg.view());

    if (msg.finalized()) {
        Debug("The HandleConsensusReply for request %lu was finalized.", reqId);
        // If we receive a finalized message, then we immediately transition
        // into the slow path.
        req->on_slow_path = true;
        if (req->transition_to_slow_path_timer) {
            req->transition_to_slow_path_timer.reset();
        }

        req->decideResult = msg.result();
        req->reply_consensus_view = msg.view();
        HandleSlowPathConsensus(reqId, msgs, true, req);
    } else if (req->on_slow_path && msgs.size() >= req->quorumSize) {
        HandleSlowPathConsensus(reqId, msgs, false, req);
    } else if (!req->on_slow_path && msgs.size() >= req->superQuorumSize) {
        HandleFastPathConsensus(reqId, msgs, req);
    }
}

void
IRClient::HandleConfirm(const TransportAddress &remote,
                        const proto::ConfirmMessage &msg)
{
    uint64_t reqId = msg.opid().clientreqid();
    auto it = pendingReqs.find(reqId);
    if (it == pendingReqs.end()) {
        Debug(
            "We received a ConfirmMessage for operation %lu, but we weren't "
            "waiting for any ConfirmMessages. We are ignoring the message.",
            reqId);
        return;
    }

    PendingRequest *req = it->second;

    viewstamp_t vs = { msg.view(), reqId };
    if (req->confirmQuorum.AddAndCheckForQuorum(vs, msg.replicaidx(), msg)) {
        req->timer->Stop();
        pendingReqs.erase(it);
        if (!req->continuationInvoked) {
            // Return to the client. ConfirmMessages are sent by replicas in
            // response to FinalizeInconsistentMessages and
            // FinalizeConsensusMessage, but inconsistent operations are
            // invoked before FinalizeInconsistentMessages are ever sent. Thus,
            // req->continuationInvoked can only be false if req is a
            // PendingConsensusRequest, so it's safe to cast it here.
            PendingConsensusRequest *r2 =
                dynamic_cast<PendingConsensusRequest *>(req);
            ASSERT(r2 != nullptr);
            if (vs.view == r2->reply_consensus_view) {
                r2->continuation(r2->request, r2->decideResult);
            } else {
                Debug(
                    "We received a majority of ConfirmMessages for request %lu "
                    "with view %lu, but the view from ReplyConsensusMessages "
                    "was %lu.",
                    reqId, vs.view, r2->reply_consensus_view);
                if (r2->error_continuation) {
                    r2->error_continuation(
                        r2->request, ErrorCode::MISMATCHED_CONSENSUS_VIEWS);
                }
            }
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
    if (req->error_continuation) {
        req->error_continuation(req->request, ErrorCode::TIMEOUT);
    }
    delete req;
}

} // namespace ir
} // namespace replication
