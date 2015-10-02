// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * lockserver/client.h:
 *   A lockserver client interface.
 *
 * Copyright 2015 Naveen Kr. Sharma <naveenks@cs.washington.edu>
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

#ifndef _IR_LOCK_CLIENT_H_
#define _IR_LOCK_CLIENT_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "lib/udptransport.h"
#include "replication/ir/client.h"
#include "store/common/promise.h"
#include "lockserver/locks-proto.pb.h"

#include <set>
#include <string>
#include <thread>

namespace lockserver {

class LockClient
{
public:
    LockClient(const std::string &configPath);
    ~LockClient();

    bool lock(const std::string &key);
    void unlock(const std::string &key);

private:
    /* Unique ID for this client. */
    uint64_t client_id;

    /* Transport layer and thread. */
    UDPTransport transport; 
    std::thread *clientTransport;

    /* Function to run the transport thread. */
    void run_client();

    /* Decide function for a lock server. */
    string Decide(const std::set<string> &results);

    /* IR client proxy. */
    replication::ir::IRClient *client;

    /* Promise to wait for pending operation. */
    Promise *waiting;

    /* Callbacks for hearing back for an operation. */
    void LockCallback(const std::string &, const std::string &);
    void UnlockCallback(const std::string &, const std::string &);
};

} // namespace lockserver

#endif /* _IR_LOCK_CLIENT_H_ */
