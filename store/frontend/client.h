// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/client.h:
 *   Interface for a multiple shard transactional client.
 *
 **********************************************************************/

#ifndef _CLIENT_API_H_
#define _CLIENT_API_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include <string>
#include <vector>

class Client
{
public:
    Client();
    ~Client();

    // Begin a transaction.
    virtual void Begin();

    // Get the value corresponding to key.
    virtual int Get(const std::string &key, std::string &value);

    // Set the value for the given key.
    virtual int Put(const std::string &key, const std::string &value);

    // Commit all Get(s) and Put(s) since Begin().
    virtual bool Commit();
    
    // Abort all Get(s) and Put(s) since Begin().
    virtual void Abort();

    // Returns statistics (vector of integers) about most recent transaction.
    virtual std::vector<int> Stats();

    // Sharding logic: Given key, generates a number b/w 0 to nshards-1
    uint64_t key_to_shard(const std::string &key, uint64_t nshards);
};

#endif /* _CLIENT_API_H_ */
