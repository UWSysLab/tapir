// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * common/versionedKVStore.h: 
 * 
 * Simple versioned key-value store that tracks the write timestamp
 * and latest read timestamp for each version.
 *
 **********************************************************************/

#ifndef _VERSIONED_KV_STORE_H_
#define _VERSIONED_KV_STORE_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "store/common/timestamp.h"

#include <set>
#include <map>
#include <unordered_map>
#include <fstream>
#include <iostream>

class VersionedKVStore
{

public:
    VersionedKVStore();
    ~VersionedKVStore();

    bool get(const std::string &key, std::pair<Timestamp, std::string> &value);
    bool get(const std::string &key, const Timestamp &t, std::pair<Timestamp, std::string> &value);
    bool getRange(const std::string &key, const Timestamp &t, std::pair<Timestamp, Timestamp> &range);
    bool getLastRead(const std::string &key, Timestamp &readTime);
    bool getLastRead(const std::string &key, const Timestamp &t, Timestamp &readTime);
    void put(const std::string &key, const std::string &value, const Timestamp &t);
    void commitGet(const std::string &key, const Timestamp &readTime, const Timestamp &commit);

private:
    struct VersionedValue {
        Timestamp write;
        std::string value;

        VersionedValue(Timestamp commit) : write(commit), value("tmp") { };
        VersionedValue(Timestamp commit, std::string val) : write(commit), value(val) { };

        friend bool operator> (const VersionedValue &v1, const VersionedValue &v2) {
            return v1.write > v2.write;
        };
        friend bool operator< (const VersionedValue &v1, const VersionedValue &v2) {
            return v1.write < v2.write;
        };
    };

    /* Global store which keeps key -> (timestamp, value) list. */
    std::unordered_map< std::string, std::set<VersionedValue> > store;
    std::unordered_map< std::string, std::map< Timestamp, Timestamp > > lastReads;
    bool inStore(const std::string &key);
    void getValue(const std::string &key, const Timestamp &t, std::set<VersionedValue>::iterator &it);
};

#endif  /* _VERSIONED_KV_STORE_H_ */
