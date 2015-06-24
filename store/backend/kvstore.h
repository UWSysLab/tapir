// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/kvstore.h:
 *   Simple versioned key-value store
 *
 **********************************************************************/

#ifndef _KV_STORE_H_
#define _KV_STORE_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"

#include <unordered_map>
#include <vector>
#include <fstream>
#include <iostream>
#include <list>

class KVStore
{

public:
    KVStore();
    ~KVStore();

    bool get(const std::string &key, std::string &value);
    bool put(const std::string &key, const std::string &value);
    bool remove(const std::string &key, std::string &value);

private:
    /* Global store which keeps key -> (timestamp, value) list. */
    std::unordered_map<std::string, std::list<std::string>> store;
};

#endif  /* _KV_STORE_H_ */
