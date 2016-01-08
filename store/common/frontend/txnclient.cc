// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/common/frontend/txnclient.cc
 *   Client interface for a single replicated shard.
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

#include "store/common/frontend/txnclient.h"

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
