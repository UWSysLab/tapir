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

#include "lib/assert.h"
#include "lib/message.h"
#include "store/common/backend/kvstore.h"
#include "store/common/timestamp.h"
#include "store/common/transaction.h"

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
