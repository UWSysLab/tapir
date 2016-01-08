// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * log.h:
 *   a replica's log of pending and committed operations
 *
 * Copyright 2013-2015 Irene Zhang <iyzhang@cs.washington.edu>
 *                     Naveen Kr. Sharma <naveenks@cs.washington.edu>
 *                     Dan R. K. Ports  <drkp@cs.washington.edu>
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

#ifndef _COMMON_LOG_IMPL_H_
#define _COMMON_LOG_IMPL_H_

template <class T> void
Log::Dump(opnum_t from, T out)
{
    for (opnum_t i = std::max(from, start);
         i <= LastOpnum(); i++) {

        const LogEntry *entry = Find(i);
        ASSERT(entry != NULL);
        
        auto elem = out->Add();
        elem->set_view(entry->viewstamp.view);
        elem->set_opnum(entry->viewstamp.opnum);
        elem->set_state(entry->state);
        elem->set_hash(entry->hash);
        *(elem->mutable_request()) = entry->request;        
    }
}

template <class iter> void
Log::Install(iter start, iter end)
{
    // Find the first divergence in the log
    iter it = start;
    for (it = start; it != end; it++) {
        const LogEntry *oldEntry = Find(it->opnum());
        if (oldEntry == NULL) {
            break;
        }
        if (it->view() != oldEntry->viewstamp.view) {
            RemoveAfter(it->opnum());
            break;
        }
    }

    if (it == end) {
        // We didn't find a divergence. This means that the logs
        // should be identical. If the existing log is longer,
        // something is wrong.
//            it--;
//            ASSERT(it->opnum() == lastViewstamp.opnum);
//            ASSERT(it->view() == lastViewstamp.view);
//            ASSERT(Find(it->opnum()+1) == NULL);
    }

    // Install the new log entries
    for (; it != end; it++) {
        viewstamp_t vs = { it->view(), it->opnum() };
        Append(vs, it->request(), LOG_STATE_PREPARED);
    }
}

#endif  /* _COMMON_LOG_IMPL_H_ */
