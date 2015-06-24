// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * spanstore/occstore.cc:
 *   Key-value store with support for OCC
 *
 **********************************************************************/

#include "spanstore/occstore.h"

using namespace std;

namespace spanstore {

OCCStore::OCCStore() : store() { }
OCCStore::~OCCStore() { }

int
OCCStore::Get(uint64_t id, const string &key, pair<Timestamp, string> &value)
{
    Debug("[%lu] GET %s", id, key.c_str());

    // Get latest from store
    if (store.get(key, value)) {
        Debug("[%lu] GET %s %lu", id, key.c_str(), value.first.getTimestamp());
        return REPLY_OK;
    } else {
        return REPLY_FAIL;
    }
}

int
OCCStore::Get(uint64_t id, const string &key, const Timestamp &timestamp, pair<Timestamp, string> &value)
{
    Debug("[%lu] GET %s", id, key.c_str());
    
    // Get version at timestamp from store
    if (store.get(key, timestamp, value)) {
        return REPLY_OK;
    } else {
        return REPLY_FAIL;
    }
}

int
OCCStore::Prepare(uint64_t id, const Transaction &txn)
{    
    Debug("[%lu] START PREPARE", id);

    if (prepared.find(id) != prepared.end()) {
        Debug("[%lu] Already prepared!", id);
        return REPLY_OK;
    }

    // Do OCC checks.
    set<string> pWrites = getPreparedWrites();
    set<string> pRW = getPreparedReadWrites();

    // Check for conflicts with the read set.
    for (auto &read : txn.getReadSet()) {
        pair<Timestamp, string> cur;
        bool ret = store.get(read.first, cur);

	    // ASSERT(ret);
        if (!ret)
            continue;

        // If this key has been written since we read it, abort.
        if (cur.first > read.second) {
            Debug("[%lu] ABORT rw conflict key:%s %lu %lu",
                  id, read.first.c_str(), cur.first.getTimestamp(),
                  read.second.getTimestamp());
            
            Abort(id);
            return REPLY_FAIL;
        }

        // If there is a pending write for this key, abort.
        if (pWrites.find(read.first) != pWrites.end()) {
            Debug("[%lu] ABORT rw conflict w/ prepared key:%s",
                  id, read.first.c_str());
            Abort(id);
            return REPLY_FAIL;
        }
    }

    // Check for conflicts with the write set.
    for (auto &write : txn.getWriteSet()) {
        // If there is a pending read or write for this key, abort.
        if (pRW.find(write.first) != pRW.end()) {
            Debug("[%lu] ABORT ww conflict w/ prepared key:%s", id,
                    write.first.c_str());
            Abort(id);
            return REPLY_FAIL;
        }
    }

    // Otherwise, prepare this transaction for commit
    prepared[id] = txn;
    Debug("[%lu] PREPARED TO COMMIT", id);
    return REPLY_OK;
}

void
OCCStore::Commit(uint64_t id, uint64_t timestamp)
{
    Debug("[%lu] COMMIT", id);
    ASSERT(prepared.find(id) != prepared.end());

    Transaction txn = prepared[id];

    for (auto &write : txn.getWriteSet()) {
        store.put(write.first, // key
                    write.second, // value
                    Timestamp(timestamp)); // timestamp
    }

    prepared.erase(id);
}

void
OCCStore::Abort(uint64_t id, const Transaction &txn)
{
    Debug("[%lu] ABORT", id);
    prepared.erase(id);
}

void
OCCStore::Load(const string &key, const string &value, const Timestamp &timestamp)
{
    store.put(key, value, timestamp);
}

set<string>
OCCStore::getPreparedWrites()
{
    // gather up the set of all writes that we are currently prepared for
    set<string> writes;
    for (auto &t : prepared) {
        for (auto &write : t.second.getWriteSet()) {
            writes.insert(write.first);
        }
    }
    return writes;
}

set<string>
OCCStore::getPreparedReadWrites()
{
    // gather up the set of all writes that we are currently prepared for
    set<string> readwrites;
    for (auto &t : prepared) {
        for (auto &write : t.second.getWriteSet()) {
            readwrites.insert(write.first);
        }
        for (auto &read : t.second.getReadSet()) {
            readwrites.insert(read.first);
        }
    }
    return readwrites;
}

} // namespace spanstore
