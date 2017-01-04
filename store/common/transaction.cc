// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * common/transaction.cc
 *   A transaction implementation.
 *
 **********************************************************************/

#include "store/common/transaction.h"

using namespace std;

Transaction::Transaction() :
    readSet(), writeSet() { }

Transaction::Transaction(const TransactionMessage &msg) 
{
    for (int i = 0; i < msg.readset_size(); i++) {
        ReadMessage readMsg = msg.readset(i);
        readSet[readMsg.key()] = Timestamp(readMsg.readtime());
    }

    for (int i = 0; i < msg.writeset_size(); i++) {
        WriteMessage writeMsg = msg.writeset(i);
        writeSet[writeMsg.key()] = writeMsg.value();
    }
}

Transaction::~Transaction() { }

const unordered_map<string, Timestamp>&
Transaction::getReadSet() const
{
    return readSet;
}

const unordered_map<string, string>&
Transaction::getWriteSet() const
{
    return writeSet;
}

void
Transaction::addReadSet(const string &key,
                        const Timestamp &readTime)
{
    readSet[key] = readTime;
}

void
Transaction::addWriteSet(const string &key,
                         const string &value)
{
    writeSet[key] = value;
}

void
Transaction::serialize(TransactionMessage *msg) const
{
    for (auto read : readSet) {
        ReadMessage *readMsg = msg->add_readset();
        readMsg->set_key(read.first);
        read.second.serialize(readMsg->mutable_readtime());
    }

    for (auto write : writeSet) {
        WriteMessage *writeMsg = msg->add_writeset();
        writeMsg->set_key(write.first);
        writeMsg->set_value(write.second);
    }
}
