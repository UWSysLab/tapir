// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/lockstore.h 

 * Single-node Key-value store with support for 2PC locking-based
 * transactions using S2PL
 *
 **********************************************************************/

#ifndef _LOCK_STORE_H_
#define _LOCK_STORE_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "common/kvstore.h"
#include "common/txnstore.h"
#include "common/transaction.h"
#include "spanstore/lockserver.h"
#include <vector>
#include <unordered_map>
#include <set>
#include <map>
#include <list>

namespace spanstore {

class LockStore : public TxnStore
{
public:
    LockStore();
    ~LockStore();

    // Overriding from TxnStore.
    int Get(uint64_t id, const std::string &key,
        std::pair<Timestamp, std::string> &value);
    int Get(uint64_t id, const std::string &key, const Timestamp &timestamp,
        std::pair<Timestamp, std::string> &value);
    int Prepare(uint64_t id, const Transaction &txn);
    void Commit(uint64_t id, uint64_t timestamp);
    void Abort(uint64_t id, const Transaction &txn);
    void Load(const std::string &key, const std::string &value,
        const Timestamp &timestamp);

private:
    // Data store.
    KVStore store;

    // Locks manager.
    LockServer locks;

    std::map<uint64_t, Transaction> prepared;

    void dropLocks(uint64_t id, const Transaction &txn);
    bool getLocks(uint64_t id, const Transaction &txn);
};

} // namespace spanstore

#endif /* _LOCK_STORE_H_ */
