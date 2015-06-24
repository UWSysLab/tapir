// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * qwstore/qwstore.h:
 *   Simple quorum write key-value store
 *
 **********************************************************************/

#ifndef _QW_STORE_H_
#define _QW_STORE_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "common/kvstore.h"
#include "common/timestamp.h"
#include "common/transaction.h"
#include "common/txnstore.h"

namespace qwstore {

class QWStore
{
private:
    KVStore store;

public:
    QWStore();
    ~QWStore();

    // add key to read set
    virtual int Get(uint64_t id, const std::string &key, std::string &value);

    // add key to write set
    virtual int Put(uint64_t id, const std::string &key, const std::string &value);

    // load keys
    virtual void Load(const std::string &key, const std::string &value);
};

} // namespace qwstore

#endif /* _QW_STORE_H_ */
