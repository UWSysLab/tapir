// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/common/backend/tests/lockserver-test.cc:
 *   test cases for simple lock server class
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

#include "store/common/backend/lockserver.h"

#include <gtest/gtest.h>

TEST(LockServer, ReadLock)
{
    LockServer s;

    EXPECT_TRUE(s.lockForRead("x", 1));
    EXPECT_TRUE(s.lockForRead("x", 2));   
    EXPECT_FALSE(s.lockForWrite("x", 3));
}

TEST(LockServer, WriteLock)
{
    LockServer s;
    
    EXPECT_TRUE(s.lockForWrite("x", 1));
    EXPECT_FALSE(s.lockForRead("x", 2));   
    EXPECT_FALSE(s.lockForWrite("x", 3));    
}
