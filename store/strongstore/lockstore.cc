// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/strongstore/lockstore.h:
 *   Key-value store with support for strong consistency using S2PL
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

#include "store/strongstore/lockstore.h"

using namespace std;

namespace strongstore {

LockStore::LockStore() : TxnStore(), store() { }
LockStore::~LockStore() { }

int
LockStore::Get(uint64_t id, const string &key, pair<Timestamp, string> &value)
{
    Debug("[%lu] GET %s", id, key.c_str());
    string val;

    if (!store.get(key, val)) {
        // couldn't find the key
        return REPLY_FAIL;
    }

    // grab the lock (ok, if we already have it)
    if (locks.lockForRead(key, id)) {
        value = make_pair(Timestamp(), val);
        return REPLY_OK;
    } else {
        Debug("[%lu] Could not acquire read lock", id);
        return REPLY_RETRY;
    }
}

int
LockStore::Get(uint64_t id, const string &key, const Timestamp &timestamp, pair<Timestamp, string> &value)
{
    return Get(id, key, value);
}

int
LockStore::Prepare(uint64_t id, const Transaction &txn)
{    
    Debug("[%lu] START PREPARE", id);

    if (prepared.size() > 100) {
        Warning("Lots of prepared transactions! %lu", prepared.size());
    }

    if (prepared.find(id) != prepared.end()) {
        Debug("[%lu] Already prepared", id);
        return REPLY_OK;
    }

    if (getLocks(id, txn)) {
        prepared[id] = txn;
        Debug("[%lu] PREPARED TO COMMIT", id);
        return REPLY_OK;
    } else {
        Debug("[%lu] Could not acquire write locks", id);
        return REPLY_RETRY;
    }
}

void
LockStore::Commit(uint64_t id, uint64_t timestamp)
{
    Debug("[%lu] COMMIT", id);
    ASSERT(prepared.find(id) != prepared.end());

    Transaction txn = prepared[id];

    for (auto &write : txn.getWriteSet()) {
        store.put(write.first, write.second);
    }

    // Drop locks.
    dropLocks(id, txn);

    prepared.erase(id);
}

void
LockStore::Abort(uint64_t id, const Transaction &txn)
{
    Debug("[%lu] ABORT", id);
    dropLocks(id, txn);
    prepared.erase(id);
}

void
LockStore::Load(const string &key, const string &value, const Timestamp &timestamp)
{
    store.put(key, value);
}

/* Used on commit and abort for second phase of 2PL. */
void
LockStore::dropLocks(uint64_t id, const Transaction &txn)
{
    for (auto &write : txn.getWriteSet()) {
        locks.releaseForWrite(write.first, id);
    }

    for (auto &read : txn.getReadSet()) {
        locks.releaseForRead(read.first, id);
    }
}

bool
LockStore::getLocks(uint64_t id, const Transaction &txn)
{
    bool ret = true;
    // if we don't have read locks, get read locks
    for (auto &read : txn.getReadSet()) {
        if (!locks.lockForRead(read.first, id)) {
            ret = false;
        }
    }
    for (auto &write : txn.getWriteSet()) {
        if (!locks.lockForWrite(write.first, id)) {
            ret = false;
        }
    }
    return ret;
}

} // namespace strongstore
