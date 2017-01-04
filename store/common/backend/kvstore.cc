// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * common/kvstore.cc:
 *   Simple versioned key-value store
 *
 * Copyright 2015 Irene Zhang <iyzhang@cs.washington.edu>
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 **********************************************************************/

#include "store/common/backend/kvstore.h"

using namespace std;

KVStore::KVStore() { }
    
KVStore::~KVStore() { }

bool
KVStore::get(const string &key, string &value)
{
    // check for existence of key in store
    if (store.find(key) == store.end() || store[key].empty()) {
        return false;
    } else {
        value = store[key].back();
	return true;
    }
}

bool
KVStore::put(const string &key, const string &value)
{
    store[key].push_back(value);
    return true;
}

/* Delete the latest version of this key. */
bool
KVStore::remove(const string &key, string &value)
{
    if (store.find(key) == store.end() || store[key].empty()) {
        return false;
    } 

    store[key].pop_back();
    return true;
}
