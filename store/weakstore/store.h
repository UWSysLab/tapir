// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * weakstore/weakstore.h:
 *   Simple quorum write key-value store with weak consistency
 *
 **********************************************************************/

#ifndef _WEAK_STORE_H_
#define _WEAK_STORE_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "store/common/backend/kvstore.h"
#include "store/common/transaction.h"

namespace weakstore {

class Store
{
private:
    KVStore store;

public:
    Store();
    ~Store();

    // add key to read set
    virtual int Get(uint64_t id, const std::string &key, std::string &value);

    // add key to write set
    virtual int Put(uint64_t id, const std::string &key, const std::string &value);

    // load keys
    virtual void Load(const std::string &key, const std::string &value);
};

} // namespace weakstore

#endif /* _WEAK_STORE_H_ */
