// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/common/promise.h
 *   Simple promise implementation.
 *
 * Copyright 2015 Irene Zhang <iyzhang@cs.washington.edu>
 *                Naveen Kr. Sharma <naveenks@cs.washington.edu>
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

#ifndef _PROMISE_H_
#define _PROMISE_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "lib/transport.h"
#include "store/common/transaction.h"

#include <condition_variable>
#include <mutex>

class Promise
{
private:
    bool done;
    int timeout;
    int reply;
    Timestamp timestamp;
    std::string value;
    std::mutex lock;
    std::condition_variable cv;

    void ReplyInternal(int r);

public:
    Promise();
    Promise(int timeoutMS); // timeout in milliseconds
    ~Promise();

    // reply to this promise and unblock any waiting threads
    void Reply(int r);
    void Reply(int r, Timestamp t);
    void Reply(int r, std::string v);
    void Reply(int r, Timestamp t, std::string v);

    // Return configured timeout
    int GetTimeout();

    // block on this until response comes back
    int GetReply();
    Timestamp GetTimestamp();
    std::string GetValue();
};

#endif /* _PROMISE_H_ */
