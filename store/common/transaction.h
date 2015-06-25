// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/transaction.h:
 *   A Transaction representation.
 *
 **********************************************************************/

#ifndef _TRANSACTION_H_
#define _TRANSACTION_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include "common/timestamp.h"
#include "common/common-proto.pb.h"

#include <unordered_map>

class Transaction {
private:
    // map between key and timestamp at
    // which the read happened and how
    // many times this key has been read
    std::unordered_map<std::string, Timestamp> readSet;

    // map between key and value(s)
    std::unordered_map<std::string, std::string> writeSet;

public:
    Transaction();
    Transaction(const TransactionMessage &msg);
    ~Transaction();

    const std::unordered_map<std::string, Timestamp>& getReadSet() const;
    const std::unordered_map<std::string, std::string>& getWriteSet() const;
    
    void addReadSet(const std::string &key, const Timestamp &readTime);
    void addWriteSet(const std::string &key, const std::string &value);
    void serialize(TransactionMessage *msg) const;
};

#endif /* _TRANSACTION_H_ */
