// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * replication/vr/client.h:
 *   dummy implementation of replication interface that just uses a
 *   single replica and passes commands directly to it
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

#ifndef _VR_CLIENT_H_
#define _VR_CLIENT_H_

#include "replication/common/client.h"
#include "lib/configuration.h"
#include "replication/vr/vr-proto.pb.h"

#include <unordered_map>

namespace replication {
namespace vr {

class VRClient : public Client
{
public:
    VRClient(const transport::Configuration &config,
             Transport *transport,
             uint64_t clientid = 0);
    virtual ~VRClient();
    virtual void Invoke(const string &request,
                        continuation_t continuation,
                        error_continuation_t error_continuation = nullptr);
    virtual void InvokeUnlogged(int replicaIdx,
                                const string &request,
                                continuation_t continuation,
                                error_continuation_t error_continuation = nullptr,
                                uint32_t timeout = DEFAULT_UNLOGGED_OP_TIMEOUT);
    virtual void ReceiveMessage(const TransportAddress &remote,
                                const string &type, const string &data);

protected:
    int view;
    int opnumber;
    uint64_t lastReqId;

    struct PendingRequest
    {
        string request;
        uint64_t clientReqId;
        continuation_t continuation;
	Timeout *timer;
        inline PendingRequest(string request,
			      uint64_t clientReqId,
                              continuation_t continuation,
			      Timeout *timer)
            : request(request), clientReqId(clientReqId),
              continuation(continuation), timer(timer) { };
	inline ~PendingRequest() { delete timer; }
    };

    struct PendingUnloggedRequest : public PendingRequest
    {
	error_continuation_t error_continuation;
        inline PendingUnloggedRequest(string request,
				      uint64_t clientReqId,
				      continuation_t continuation,
				      Timeout *timer,
				      error_continuation_t error_continuation)
            : PendingRequest(request, clientReqId, continuation, timer),
              error_continuation(error_continuation) { };
    };

    std::unordered_map<uint64_t, PendingRequest *> pendingReqs;

    void SendRequest(const PendingRequest *req);
    void ResendRequest(const uint64_t reqId);
    void HandleReply(const TransportAddress &remote,
                     const proto::ReplyMessage &msg);
    void HandleUnloggedReply(const TransportAddress &remote,
                             const proto::UnloggedReplyMessage &msg);
    void UnloggedRequestTimeoutCallback(const uint64_t reqId);
};

} // namespace replication::vr
} // namespace replication

#endif  /* _VR_CLIENT_H_ */
