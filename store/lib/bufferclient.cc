// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/bufferclient.cc:
 *   Single shard buffering client implementation.
 *
 **********************************************************************/

#include "common/bufferclient.h"
#include "common/txnstore.h"

using namespace std;

BufferClient::BufferClient(TxnClient* txnclient) : txn()
{
    this->txnclient = txnclient;
}

BufferClient::~BufferClient() { }

/* Begins a transaction. */
void
BufferClient::Begin(uint64_t tid)
{
    // Initialize data structures.
    txn = Transaction();
    this->tid = tid;
    txnclient->Begin(tid);
}

/* Get value for a key.
 * Returns 0 on success, else -1. */
void
BufferClient::Get(const string &key, Promise *promise)
{
    // Read your own writes, check the write set first.
    if (txn.getWriteSet().find(key) != txn.getWriteSet().end()) {
        promise->Reply(REPLY_OK, (txn.getWriteSet().find(key))->second);
        return;
    }

    // Consistent reads, check the read set.
    if (txn.getReadSet().find(key) != txn.getReadSet().end()) {
        // read from the server at same timestamp.
        txnclient->Get(tid, key, (txn.getReadSet().find(key))->second, promise);
        return;
    }
    
    // Otherwise, get latest value from server.
    Promise p(GET_TIMEOUT);
    Promise *pp = (promise != NULL) ? promise : &p;

    txnclient->Get(tid, key, pp);
    if (pp->GetReply() == REPLY_OK) {
        Debug("Adding [%s] with ts %lu", key.c_str(), pp->GetTimestamp().getTimestamp());
        txn.addReadSet(key, pp->GetTimestamp());
    }
}

/* Set value for a key. (Always succeeds).
 * Returns 0 on success, else -1. */
void
BufferClient::Put(const string &key, const string &value, Promise *promise)
{
    // Update the write set.
    txn.addWriteSet(key, value);
    promise->Reply(REPLY_OK);
}

/* Prepare the transaction. */
void
BufferClient::Prepare(const Timestamp &timestamp, Promise *promise)
{
    txnclient->Prepare(tid, txn, timestamp, promise);
}

void
BufferClient::Commit(uint64_t timestamp, Promise *promise)
{
    txnclient->Commit(tid, txn, timestamp, promise);
}

/* Aborts the ongoing transaction. */
void
BufferClient::Abort(Promise *promise)
{
    txnclient->Abort(tid, Transaction(), promise);
}
