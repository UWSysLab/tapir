// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/txnclient.cc:
 *   Interface for a single shard transactional client.
 *
 **********************************************************************/

#include "common/txnclient.h"

using namespace std;

TxnClient::TxnClient() { }
TxnClient::~TxnClient() { }

void
TxnClient::Begin(uint64_t id)
{
    Panic("Unimplemented BEGIN");
}
    
void
TxnClient::Get(uint64_t id,
               const string &key,
               Promise *promise)
{
    Panic("Unimplemented GET");
    return;
}

void
TxnClient::Get(uint64_t id, 
               const string &key,
               const Timestamp &timestamp,
               Promise *promise)
{
    Panic("Unimplemented GET");
    return;
}

void
TxnClient::Put(uint64_t id,
               const string &key,
               const string &value,
               Promise *promise)
{
    Panic("Unimplemented PUT");
    return;
}

void
TxnClient::Prepare(uint64_t id,
                   const Transaction &txn,
                   const Timestamp &timestamp,
                   Promise *promise)
{
    Panic("Unimplemented PREPARE");
}

void
TxnClient::Commit(uint64_t id,
                  const Transaction &txn,
                  uint64_t timestamp,
                  Promise *promise)
{
    Panic("Unimplemented COMMIT");
    return;
}
    
void
TxnClient::Abort(uint64_t id,
                 const Transaction &txn,
                 Promise *promise)
{
    Panic("Unimplemented ABORT");
    return;
}
