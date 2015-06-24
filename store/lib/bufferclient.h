// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/bufferclient.h:
 *   Single shard buffering client header.
 *
 **********************************************************************/

#ifndef _BUFFER_CLIENT_H_
#define _BUFFER_CLIENT_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "paxos-lib/common/client.h"
#include "common/transaction.h"
#include "common/promise.h"
#include "common/txnclient.h"

#include <string>

class BufferClient
{
public:
    BufferClient(TxnClient *txnclient);
    ~BufferClient();

    // Begin a transaction with given tid.
    void Begin(uint64_t tid);

    // Get value corresponding to key.
    void Get(const string &key, Promise *promise = NULL);

    // Put value for given key.
    void Put(const string &key, const string &value, Promise *promise = NULL);

    // Prepare (Spanner requires a prepare timestamp)
    void Prepare(const Timestamp &timestamp = Timestamp(), Promise *promise = NULL); 

    // Commit the ongoing transaction.
    void Commit(uint64_t timestamp = 0, Promise *promise = NULL);

    // Abort the running transaction.
    void Abort(Promise *promise = NULL);

private:
    // Underlying single shard transaction client implementation.
    TxnClient* txnclient;

    // Transaction to keep track of read and write set.
    Transaction txn;

    // Unique transaction id to keep track of ongoing transaction.
    uint64_t tid;
};

#endif /* _BUFFER_CLIENT_H_ */
