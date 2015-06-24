// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/promise.cc:
 *   Interface for blocking on an async response.
 *
 **********************************************************************/

#include "common/promise.h"

using namespace std;

Promise::Promise() 
{ 
    done = false;
    reply = 0;
    timeout = 1000;
}

Promise::Promise(int timeoutMS) 
{ 
    done = false;
    reply = 0;
    timeout = timeoutMS;
}

Promise::~Promise() { }

// Get configured timeout, return after this period
int
Promise::GetTimeout()
{
    return timeout;
}

// Functions for replying to the promise
void
Promise::ReplyInternal(int r)
{
    done = true;
    reply = r;
    cv.notify_all();
}

void
Promise::Reply(int r)
{
    lock_guard<mutex> l(lock);
    ReplyInternal(r);
}

void
Promise::Reply(int r, Timestamp t)
{
    lock_guard<mutex> l(lock);
    timestamp = t;
    ReplyInternal(r);
}

void
Promise::Reply(int r, string v)
{
    lock_guard<mutex> l(lock);
    value = v;
    ReplyInternal(r);
}

void
Promise::Reply(int r, Timestamp t, string v)
{
    lock_guard<mutex> l(lock);
    value = v;
    timestamp = t;
    ReplyInternal(r);
}

// Functions for getting a reply from the promise
int
Promise::GetReply()
{
    unique_lock<mutex> l(lock);
    while(!done) {
        cv.wait(l);
    }
    return reply;
}

Timestamp
Promise::GetTimestamp()
{
    unique_lock<mutex> l(lock);
    while(!done) {
        cv.wait(l);
    }
    return timestamp;
}
    
string
Promise::GetValue()
{
    unique_lock<mutex> l(lock);
    while(!done) {
        cv.wait(l);
    }
    return value;
}
