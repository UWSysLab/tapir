// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/txnclient.h:
 *   Interface for a single shard transactional client.
 *
 **********************************************************************/

#ifndef _TXN_CLIENT_H_
#define _TXN_CLIENT_H_

#include "common/timestamp.h"
#include "common/promise.h"
#include "common/transaction.h"
#include <string>

#define DEFAULT_TIMEOUT_MS 250
#define DEFAULT_MULTICAST_TIMEOUT_MS 500

// Timeouts for various operations
#define GET_TIMEOUT 250
#define GET_RETRIES 3
// Only used for QWStore
#define PUT_TIMEOUT 250
#define PREPARE_TIMEOUT 1000
#define PREPARE_RETRIES 5

#define COMMIT_TIMEOUT 1000
#define COMMIT_RETRIES 5

#define ABORT_TIMEOUT 1000
#define RETRY_TIMEOUT 500000



class TxnClient
{
public:
    TxnClient();
    ~TxnClient();

    // Begin a transaction.
    virtual void Begin(uint64_t id);
    
    // Get the value corresponding to key (valid at given timestamp).
    virtual void Get(uint64_t id,
                     const std::string &key,
                     Promise *promise = NULL);

    virtual void Get(uint64_t id,
                     const std::string &key,
                     const Timestamp &timestamp,
                     Promise *promise = NULL);

    // Set the value for the given key.
    virtual void Put(uint64_t id,
                     const std::string &key,
                     const std::string &value,
                     Promise *promise = NULL);

    // Prepare the transaction.
    virtual void Prepare(uint64_t id,
                         const Transaction &txn,
                         const Timestamp &timestamp = Timestamp(),
                         Promise *promise = NULL);

    // Commit all Get(s) and Put(s) since Begin().
    virtual void Commit(uint64_t id,
                        const Transaction &txn = Transaction(), 
                        uint64_t timestamp = 0,
                        Promise *promise = NULL);
    
    // Abort all Get(s) and Put(s) since Begin().
    virtual void Abort(uint64_t id, 
                       const Transaction &txn = Transaction(), 
                       Promise *promise = NULL);
};

#endif /* _TXN_CLIENT_H_ */
