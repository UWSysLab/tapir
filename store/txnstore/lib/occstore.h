// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * spanstore/occstore.h:
 *   Key-value store with support for transactions using OCC.
 *
 **********************************************************************/

#ifndef _OCC_STORE_H_
#define _OCC_STORE_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "common/versionedKVStore.h"
#include "common/txnstore.h"
#include "common/transaction.h"

#include <vector>
#include <unordered_map>
#include <set>
#include <map>
#include <list>

namespace spanstore {

class OCCStore : public TxnStore
{
public:
    OCCStore();
    ~OCCStore();

    // Overriding from TxnStore.
    int Get(uint64_t id, const std::string &key, std::pair<Timestamp, std::string> &value);
    int Get(uint64_t id, const std::string &key, const Timestamp &timestamp, std::pair<Timestamp, std::string> &value);
    int Prepare(uint64_t id, const Transaction &txn);
    void Commit(uint64_t id, uint64_t timestamp);
    void Abort(uint64_t id, const Transaction &txn = Transaction());
    void Load(const std::string &key, const std::string &value, const Timestamp &timestamp);

private:
    // Data store.
    VersionedKVStore store;

    std::map<uint64_t, Transaction> prepared;

    std::set<std::string> getPreparedWrites();
    std::set<std::string> getPreparedReadWrites();
};

} // namespace spanstore

#endif /* _OCC_STORE_H_ */
