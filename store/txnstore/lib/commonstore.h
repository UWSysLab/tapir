// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/txnstore.h:
 *   Interface for a single node transactional store serving as a
 *   server-side backend
 *
 **********************************************************************/

#ifndef _TXN_STORE_H_
#define _TXN_STORE_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "common/transaction.h"
#include "common/timestamp.h"

// Reply types
#define REPLY_OK 0
#define REPLY_FAIL 1
#define REPLY_RETRY 2
#define REPLY_ABSTAIN 3
#define REPLY_TIMEOUT 4
#define REPLY_NETWORK_FAILURE 5
#define REPLY_MAX 6

class TxnStore
{
public:

    TxnStore();
    virtual ~TxnStore();

    // add key to read set
    virtual int Get(uint64_t id, const std::string &key,
        std::pair<Timestamp, std::string> &value);

    virtual int Get(uint64_t id, const std::string &key,
        const Timestamp &timestamp, std::pair<Timestamp, std::string> &value);

    // add key to write set
    virtual int Put(uint64_t id, const std::string &key,
        const std::string &value);

    // check whether we can commit this transaction (and lock the read/write set)
    virtual int Prepare(uint64_t id, const Transaction &txn);

    virtual int Prepare(uint64_t id, const Transaction &txn,
        const Timestamp &timestamp, Timestamp &proposed);

    // commit the transaction
    virtual void Commit(uint64_t id, uint64_t timestamp = 0);

    // abort a running transaction
    virtual void Abort(uint64_t id, const Transaction &txn = Transaction());

    // load keys
    virtual void Load(const std::string &key, const std::string &value,
        const Timestamp &timestamp);
};

#endif /* _TXN_STORE_H_ */
