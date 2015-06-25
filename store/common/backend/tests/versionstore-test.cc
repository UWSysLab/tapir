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

TEST(VersionedKVStore, Put)
{
    VersionedKVStore store;

    EXPECT_TRUE(store.put("test1", "abc"));
    EXPECT_TRUE(store.put("test2", "def"));
    EXPECT_TRUE(store.put("test1", "xyz"));
    EXPECT_TRUE(store.put("test3", "abc"));
}

TEST(VersionedKVStore, Get)
{
    VersionedKVStore store;
    pair<Timestamp, std::string> val;

    EXPECT_TRUE(store.put("test1", "abc"));
    EXPECT_TRUE(store.get("test1", val));
    EXPECT_EQ(val[1], "abc");

    EXPECT_TRUE(store.put("test2", "def"));
    EXPECT_TRUE(store.get("test2", val));
    EXPECT_EQ(val[1], "def");

    EXPECT_TRUE(store.put("test1", "xyz"));
    EXPECT_TRUE(store.get("test1", val));
    EXPECT_EQ(val[1], "xyz");
}

TEST(VersionedKVStore, VersionedGet)
{
    VersionedKVStore store;
    Timestamp time;
    Timestamp time2;
    std::string val;

    EXPECT_TRUE(store.put("test1", "abc", time));
    EXPECT_TRUE(store.get("test1", val, time));
    EXPECT_EQ(val, "abc");

    EXPECT_TRUE(store.put("test2", "def", time2));
    EXPECT_TRUE(store.get("test2", val, time2));
    EXPECT_EQ(val, "def");

    EXPECT_TRUE(store.put("test1", "xyz", time2));
    EXPECT_TRUE(store.get("test1", val, time2));
    EXPECT_EQ(val, "xyz");
    
    EXPECT_TRUE(store.get("test1", val, time));
    EXPECT_EQ(val, "abc");
}
