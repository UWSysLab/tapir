// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * memory.cc:
 *   parsing and pretty-printing of memory sizes
 *
 * Copyright 2013 Dan R. K. Ports  <drkp@cs.washington.edu>
 * Copyright 2009-2012 Massachusetts Institute of Technology
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

#include "memory.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

char *
Memory_FmtSize(char *buf, size_t n)
{
    char suffix = 0;
    if ((n & 0x3ff) == 0) {
        n >>= 10;
        suffix = 'K';
    }
    if ((n & 0x3ff) == 0) {
        n >>= 10;
        suffix = 'M';
    }
    if ((n & 0x3ff) == 0) {
        n >>= 10;
        suffix = 'G';
    }
    if (suffix) {
        sprintf(buf, "%llu%c", (unsigned long long)n, suffix);
    } else {
        sprintf(buf, "%llu", (unsigned long long)n);
    }
    return buf;
}

static unsigned long long
Memory_ReadSize1(const char *buf, const char **endPtr)
{
    unsigned long long res = strtoull(buf, (char **)endPtr, 0);
    switch (**endPtr) {
    case 'G':
    case 'g':
        res <<= 10;
    case 'M':
    case 'm':
        res <<= 10;
    case 'K':
    case 'k':
        res <<= 10;
        ++(*endPtr);
    }
    return res;
}

size_t
Memory_ReadSize(const char *buf, const char **endPtr)
{
    unsigned long long ret = 0;
    bool more;

    do {
        ret += Memory_ReadSize1(buf, &buf);
        if (*buf == '+' && *(buf+1)) {
            more = true;
            ++buf;
        } else {
            more = false;
        }
    } while (more);

    if (endPtr)
        *endPtr = buf;
    return (size_t)ret;
}
