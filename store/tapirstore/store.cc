// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/tapirstore/store.cc:
 *   Key-value store with support for transactions using TAPIR.
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

#include "store/tapirstore/store.h"

namespace tapirstore {

using namespace std;

Store::Store(bool linearizable) : linearizable(linearizable), store() { }

Store::~Store() { }

int
Store::Get(uint64_t id, const string &key, pair<Timestamp,string> &value)
{
    Debug("[%lu] GET %s", id, key.c_str());

    bool ret = store.get(key, value);
    if (ret) {
        Debug("Value: %s at <%lu, %lu>", value.second.c_str(), value.first.getTimestamp(), value.first.getID());
        return REPLY_OK;
    } else {
        return REPLY_FAIL;
    }
}

int
Store::Get(uint64_t id, const string &key, const Timestamp &timestamp, pair<Timestamp,string> &value)
{
    Debug("[%lu] GET %s at <%lu, %lu>", id, key.c_str(), timestamp.getTimestamp(), timestamp.getID());

    bool ret = store.get(key, timestamp, value);
    if (ret) {
        return REPLY_OK;
    } else {
        return REPLY_FAIL;
    }
}

int
Store::Prepare(uint64_t id, const Transaction &txn, const Timestamp &timestamp, Timestamp &proposedTimestamp)
{   
    Debug("[%lu] START PREPARE", id);

    if (prepared.find(id) != prepared.end()) {
        if (prepared[id].first == timestamp) {
            Warning("[%lu] Already Prepared!", id);
            return REPLY_OK;
        } else {
            // run the checks again for a new timestamp
            prepared.erase(id);
        }
    }

    // do OCC checks
    unordered_map<string, set<Timestamp>> pWrites;
    GetPreparedWrites(pWrites);
    unordered_map<string, set<Timestamp>> pReads;
    GetPreparedReads(pReads);

    // check for conflicts with the read set
    for (auto &read : txn.getReadSet()) {
        pair<Timestamp, Timestamp> range;
        bool ret = store.getRange(read.first, read.second, range);

        // if we don't have this key then no conflicts for read
        if (!ret) continue;

        // if we don't have this version then no conflicts for read
        if (range.first != read.second) continue;

        // if the value is still valid
        if (!range.second.isValid()) {
            // check pending writes.
            if ( pWrites.find(read.first) != pWrites.end() && 
                 (linearizable || 
                  pWrites[read.first].upper_bound(timestamp) != pWrites[read.first].begin()) ) {
                Debug("[%lu] ABSTAIN rw conflict w/ prepared key:%s",
                      id, read.first.c_str());
                return REPLY_ABSTAIN;
            }

        } else if (linearizable || timestamp > range.second) {
            /* if value is not still valid, if we are running linearizable, then abort.
             *  Else check validity range. if
             * proposed timestamp not within validity range, then
             * conflict and abort
             */
            ASSERT(timestamp > range.first);
            Debug("[%lu] ABORT rw conflict key:%s",
                  id, read.first.c_str());
            return REPLY_FAIL;
        } else {
            /* there may be a pending write in the past.  check
             * pending writes again.  If proposed transaction is
             * earlier, abstain
             */
            if (pWrites.find(read.first) != pWrites.end()) {
                for (auto &writeTime : pWrites[read.first]) {
                    if (writeTime > range.first && 
                        writeTime < timestamp) {
                        Debug("[%lu] ABSTAIN rw conflict w/ prepared key:%s",
                              id, read.first.c_str());
                        return REPLY_ABSTAIN;
                    }
                }
            }
        }
    }

    // check for conflicts with the write set
    for (auto &write : txn.getWriteSet()) {
        pair<Timestamp, string> val;
        // if this key is in the store
        if ( store.get(write.first, val) ) {
            Timestamp lastRead;
            bool ret;

            // if the last committed write is bigger than the timestamp,
            // then can't accept in linearizable
            if ( linearizable && val.first > timestamp ) {
                Debug("[%lu] RETRY ww conflict w/ prepared key:%s", 
                      id, write.first.c_str());
                proposedTimestamp = val.first;
                return REPLY_RETRY;	                    
            }

            // if last committed read is bigger than the timestamp, can't
            // accept this transaction, but can propose a retry timestamp

            // if linearizable mode, then we get the timestamp of the last
            // read ever on this object
            if (linearizable) {
                ret = store.getLastRead(write.first, lastRead);
            } else {
                // otherwise, we get the last read for the version that is being written
                ret = store.getLastRead(write.first, timestamp, lastRead);
            }

            // if this key is in the store and has been read before
            if (ret && lastRead > timestamp) {
                Debug("[%lu] RETRY wr conflict w/ prepared key:%s", 
                      id, write.first.c_str());
                proposedTimestamp = lastRead;
                return REPLY_RETRY; 
            }
        }


        // if there is a pending write for this key, greater than the
        // proposed timestamp, retry
        if ( linearizable &&
             pWrites.find(write.first) != pWrites.end()) {
            set<Timestamp>::iterator it = pWrites[write.first].upper_bound(timestamp);
            if ( it != pWrites[write.first].end() ) {
                Debug("[%lu] RETRY ww conflict w/ prepared key:%s",
                      id, write.first.c_str());
                proposedTimestamp = *it;
                return REPLY_RETRY;
            }
        }


        //if there is a pending read for this key, greater than the
        //propsed timestamp, abstain
        if ( pReads.find(write.first) != pReads.end() &&
             pReads[write.first].upper_bound(timestamp) != pReads[write.first].end() ) {
            Debug("[%lu] ABSTAIN wr conflict w/ prepared key:%s", 
                  id, write.first.c_str());
            return REPLY_ABSTAIN;
        }
    }

    // Otherwise, prepare this transaction for commit
    prepared[id] = make_pair(timestamp, txn);
    Debug("[%lu] PREPARED TO COMMIT", id);

    return REPLY_OK;
}
    
void
Store::Commit(uint64_t id, uint64_t timestamp)
{

    Debug("[%lu] COMMIT", id);
    
    // Nope. might not find it
    //ASSERT(prepared.find(id) != prepared.end());

    pair<Timestamp, Transaction> p = prepared[id];

    Commit(p.first, p.second);

    prepared.erase(id);
}

void
Store::Commit(const Timestamp &timestamp, const Transaction &txn)
{
    // updated timestamp of last committed read for the read set
    for (auto &read : txn.getReadSet()) {
        store.commitGet(read.first, // key
                        read.second, // timestamp of read version
                        timestamp); // commit timestamp
    }

    // insert writes into versioned key-value store
    for (auto &write : txn.getWriteSet()) {
        store.put(write.first, // key
                  write.second, // value
                  timestamp); // timestamp
    }
}

void
Store::Abort(uint64_t id, const Transaction &txn)
{
    Debug("[%lu] ABORT", id);
    
    if (prepared.find(id) != prepared.end()) {
        prepared.erase(id);
    }
}

void
Store::Load(const string &key, const string &value, const Timestamp &timestamp)
{
    store.put(key, value, timestamp);
}

void
Store::GetPreparedWrites(unordered_map<string, set<Timestamp>> &writes)
{
    // gather up the set of all writes that are currently prepared
    for (auto &t : prepared) {
        for (auto &write : t.second.second.getWriteSet()) {
            writes[write.first].insert(t.second.first);
        }
    }
}

void
Store::GetPreparedReads(unordered_map<string, set<Timestamp>> &reads)
{
    // gather up the set of all writes that are currently prepared
    for (auto &t : prepared) {
        for (auto &read : t.second.second.getReadSet()) {
            reads[read.first].insert(t.second.first);
        }
    }
}

} // namespace tapirstore
