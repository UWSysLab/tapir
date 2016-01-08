// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * client.h:
 *   interface to replication client stubs
 *
 * Copyright 2013-2015 Irene Zhang <iyzhang@cs.washington.edu>
 *                     Naveen Kr. Sharma <naveenks@cs.washington.edu>
 *                     Dan R. K. Ports  <drkp@cs.washington.edu>
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

#ifndef _COMMON_CLIENT_H_
#define _COMMON_CLIENT_H_

#include "lib/configuration.h"
#include "replication/common/request.pb.h"
#include "lib/transport.h"


#include <functional>

namespace replication {

class Client : public TransportReceiver
{
public:
    typedef std::function<void (const string &, const string &)> continuation_t;
    typedef std::function<void (const string &)> timeout_continuation_t;

    static const uint32_t DEFAULT_UNLOGGED_OP_TIMEOUT = 1000; // milliseconds
    
    Client(const transport::Configuration &config, Transport *transport,
           uint64_t clientid = 0);
    virtual ~Client();
    virtual void Invoke(const string &request,
                        continuation_t continuation) = 0;
    virtual void InvokeUnlogged(int replicaIdx,
                                const string &request,
                                continuation_t continuation,
                                timeout_continuation_t timeoutContinuation = nullptr,
                                uint32_t timeout = DEFAULT_UNLOGGED_OP_TIMEOUT) = 0;
    virtual void ReceiveMessage(const TransportAddress &remote,
                                const string &type,
                                const string &data);
    
protected:
    transport::Configuration config;
    Transport *transport;
    
    uint64_t clientid;
};

} // namespace replication

#endif  /* _COMMON_CLIENT_H_ */
