// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * qwstore/qwstore.cc:
 *   Simple quorum write key-value store implementation
 *
 **********************************************************************/

#include "qwstore.h"

using namespace std;

namespace qwstore {

QWStore::QWStore() { }
QWStore::~QWStore() { }

int
QWStore::Get(uint64_t id, const string &key, string &value)
{
    Debug("[%lu] GET %s", id, key.c_str());
    string val;
    if (store.get(key, val)) {
        value = val;
        return REPLY_OK;
    }
    return REPLY_FAIL;
}


int
QWStore::Put(uint64_t id, const string &key, const string &value)
{
    Debug("[%lu] PUT %s %s", id, key.c_str(), value.c_str());
    store.put(key, value);
    return REPLY_OK;
}

void
QWStore::Load(const string &key, const string &value)
{
    store.put(key, value);
}

} // namespace qwstore
