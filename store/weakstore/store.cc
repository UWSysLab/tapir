// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/weakstore/weakstore.cc:
 *   Simple quorum write key-value store implementation with weak consistency
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

#include "store/weakstore/store.h"

namespace weakstore {

using namespace std;

Store::Store() { }
Store::~Store() { }

int
Store::Get(uint64_t id, const string &key, string &value)
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
Store::Put(uint64_t id, const string &key, const string &value)
{
    Debug("[%lu] PUT %s %s", id, key.c_str(), value.c_str());
    store.put(key, value);
    return REPLY_OK;
}

void
Store::Load(const string &key, const string &value)
{
    store.put(key, value);
}

} // namespace weakstore
