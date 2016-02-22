// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * replication/ir/client.h:
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

#ifndef _IR_CLIENT_H_
#define _IR_CLIENT_H_

#include "replication/common/client.h"
#include "replication/common/quorumset.h"
#include "lib/configuration.h"
#include "replication/ir/ir-proto.pb.h"

#include <functional>
#include <set>

namespace replication {
namespace ir {

class IRClient : public Client
{
public:
    typedef std::function<string (const std::set<string> &)> decide_t; 
    
    IRClient(const transport::Configuration &config,
             Transport *transport,
             uint64_t clientid = 0);
    virtual ~IRClient();
    virtual void Invoke(const string &request,
                        continuation_t continuation);
    virtual void InvokeInconsistent(const string &request,
                                    continuation_t continuation);
    virtual void InvokeConsensus(const string &request,
                                 decide_t decide,
                                 continuation_t continuation);
    virtual void InvokeUnlogged(int replicaIdx,
                                const string &request,
                                continuation_t continuation,
                                timeout_continuation_t timeoutContinuation = nullptr,
                                uint32_t timeout = DEFAULT_UNLOGGED_OP_TIMEOUT);
    virtual void ReceiveMessage(const TransportAddress &remote,
                                const string &type, const string &data);

protected:
    uint64_t view;
    uint64_t lastReqId;
    QuorumSet<viewstamp_t, proto::ReplyInconsistentMessage> inconsistentReplyQuorum;
    QuorumSet<viewstamp_t, proto::ReplyConsensusMessage> consensusReplyQuorum;
    QuorumSet<viewstamp_t, proto::ConfirmMessage> confirmQuorum;

    struct PendingRequest
    {
        string request;
        string decideReq;
        uint64_t clientReqId;
        decide_t decide;
        continuation_t continuation;
        timeout_continuation_t timeoutContinuation;
        
        inline PendingRequest(string request, uint64_t clientReqId,
                              continuation_t continuation)
            : request(request), clientReqId(clientReqId),
              continuation(continuation) { }
    };
    PendingRequest *pendingInconsistentRequest;
    PendingRequest *pendingConsensusRequest;
    PendingRequest *pendingUnloggedRequest;
    Timeout *inconsistentRequestTimeout;
    Timeout *consensusRequestTimeout;
    Timeout *confirmationTimeout;
    Timeout *unloggedRequestTimeout;

    void SendInconsistent();
    void ResendInconsistent();
    void ConsensusSlowPath();
    void ResendConfirmation();
    void HandleInconsistentReply(const TransportAddress &remote,
                                 const proto::ReplyInconsistentMessage &msg);
    void HandleConsensusReply(const TransportAddress &remote,
                     const proto::ReplyConsensusMessage &msg);
    void HandleConfirm(const TransportAddress &remote,
                       const proto::ConfirmMessage &msg);
    void HandleUnloggedReply(const TransportAddress &remote,
                             const proto::UnloggedReplyMessage &msg);
    void UnloggedRequestTimeoutCallback();
};

} // namespace replication::ir
} // namespace replication

#endif  /* _IR_CLIENT_H_ */
