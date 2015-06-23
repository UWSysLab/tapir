// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * viewstamp.h:
 *   definition of types and utility functions for viewstamps and
 *   related types
 *
 * Copyright 2013 Dan R. K. Ports  <drkp@cs.washington.edu>
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

#ifndef _LIB_VIEWSTAMP_H_
#define _LIB_VIEWSTAMP_H_

#define __STDC_FORMAT_MACROS
#include <inttypes.h>

typedef uint64_t view_t;
typedef uint64_t opnum_t;

struct viewstamp_t
{
    view_t view;
    opnum_t opnum;

    viewstamp_t() : view(0), opnum(0) {}
    viewstamp_t(view_t view, opnum_t opnum) : view(view), opnum(opnum) {}
};

#define FMT_VIEW "%" PRIu64
#define FMT_OPNUM "%" PRIu64

#define FMT_VIEWSTAMP "<" FMT_VIEW "," FMT_OPNUM ">"
#define VA_VIEWSTAMP(x) x.view, x.opnum

static inline int
Viewstamp_Compare(viewstamp_t a, viewstamp_t b)
{
    if (a.view < b.view) return -1;
    if (a.view > b.view) return 1;
    if (a.opnum < b.opnum) return -1;
    if (a.opnum > b.opnum) return 1;
    return 0;
}

inline bool operator==(const viewstamp_t& lhs, const viewstamp_t& rhs){ return Viewstamp_Compare(lhs,rhs) == 0; }
inline bool operator!=(const viewstamp_t& lhs, const viewstamp_t& rhs){return !operator==(lhs,rhs);}
inline bool operator< (const viewstamp_t& lhs, const viewstamp_t& rhs){ return Viewstamp_Compare(lhs,rhs) < 0; }
inline bool operator> (const viewstamp_t& lhs, const viewstamp_t& rhs){return  operator< (rhs,lhs);}
inline bool operator<=(const viewstamp_t& lhs, const viewstamp_t& rhs){return !operator> (lhs,rhs);}
inline bool operator>=(const viewstamp_t& lhs, const viewstamp_t& rhs){return !operator< (lhs,rhs);}

#endif  /* _LIB_VIEWSTAMP_H_ */
