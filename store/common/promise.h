// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/promise.h:
 *   Interface for blocking on an async response.
 *
 **********************************************************************/

#ifndef _PROMISE_H_
#define _PROMISE_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "lib/transport.h"
#include "transaction.h"
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
