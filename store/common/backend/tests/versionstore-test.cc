// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/common/backend/tests/versionstore-test.cc
 *   test cases for simple versioned key-value store class
 *
 * Copyright 2015 Irene Zhang  <iyzhang@cs.washington.edu>
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

#include "store/common/backend/versionstore.h"

#include <gtest/gtest.h>

TEST(VersionedKVStore, Get)
{
    VersionedKVStore store;
    std::pair<Timestamp, std::string> val;

    store.put("test1", "abc", Timestamp(10));
    EXPECT_TRUE(store.get("test1", val));
    EXPECT_EQ(val.second, "abc");
    EXPECT_EQ(Timestamp(10), val.first); 

    store.put("test2", "def", Timestamp(10));
    EXPECT_TRUE(store.get("test2", val));
    EXPECT_EQ(val.second, "def");
    EXPECT_EQ(Timestamp(10), val.first); 

    store.put("test1", "xyz", Timestamp(11));
    EXPECT_TRUE(store.get("test1", val));
    EXPECT_EQ(val.second, "xyz");
    EXPECT_EQ(Timestamp(11), val.first); 
    
    EXPECT_TRUE(store.get("test1", Timestamp(10), val));
    EXPECT_EQ(val.second, "abc");
}
