// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * log.h:
 *   a replica's log of pending and committed operations
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

#include "replication/common/log.h"
#include "replication/common/request.pb.h"
#include "lib/assert.h"

#include <openssl/sha.h>

namespace replication {

const string Log::EMPTY_HASH = string(SHA_DIGEST_LENGTH, '\0');

Log::Log(bool useHash, opnum_t start, string initialHash)
    : useHash(useHash)
{
    this->initialHash = initialHash;
    this->start = start;
    if (start == 1) {
        ASSERT(initialHash == EMPTY_HASH);
    }
}


LogEntry &
Log::Append(viewstamp_t vs, const Request &req, LogEntryState state)
{
    if (entries.empty()) {
        ASSERT(vs.opnum == start);
    } else {
        ASSERT(vs.opnum == LastOpnum()+1);
    }
    
    LogEntry entry;
    entry.viewstamp = vs;
    entry.request = req;
    entry.state = state;
    if (useHash) {
        entry.hash = ComputeHash(LastHash(), entry);        
    }

    entries.push_back(entry);
    return *Find(vs.opnum);
}

// This really ought to be const
LogEntry *
Log::Find(opnum_t opnum)
{
    if (entries.empty()) {
        return NULL;
    }

    if (opnum < start) {
        return NULL;
    }

    if (opnum-start > entries.size()-1) {
        return NULL;
    }

    LogEntry *entry = &entries[opnum-start];
    ASSERT(entry->viewstamp.opnum == opnum);
    return entry;
}


bool
Log::SetStatus(opnum_t op, LogEntryState state)
{
    LogEntry *entry = Find(op);
    if (entry == NULL) {
        return false;
    }

    entry->state = state;
    return true;
}

bool
Log::SetRequest(opnum_t op, const Request &req)
{
    if (useHash) {
        Panic("Log::SetRequest on hashed log not supported.");
    }
    
    LogEntry *entry = Find(op);
    if (entry == NULL) {
        return false;
    }

    entry->request = req;
    return true;
}

void
Log::RemoveAfter(opnum_t op)
{
#if PARANOID
    // We'd better not be removing any committed entries.
    for (opnum_t i = op; i <= LastOpnum(); i++) {
        ASSERT(Find(i)->state != LOG_STATE_COMMITTED);
    }
#endif

    if (op > LastOpnum()) {
        return;
    }

    Debug("Removing log entries after " FMT_OPNUM, op);

    ASSERT(op-start < entries.size());
    entries.resize(op-start);

    ASSERT(LastOpnum() == op-1);
}

LogEntry *
Log::Last()
{
    if (entries.empty()) {
        return NULL;
    }
    
    return &entries.back();
}

viewstamp_t
Log::LastViewstamp() const
{
    if (entries.empty()) {
        return viewstamp_t(0, start-1);
    } else {
        return entries.back().viewstamp;
    }
}

opnum_t
Log::LastOpnum() const
{
    if (entries.empty()) {
        return start-1;
    } else {
        return entries.back().viewstamp.opnum;
    }
}

opnum_t
Log::FirstOpnum() const
{
    // XXX Not really sure what's appropriate to return here if the
    // log is empty
    return start;
}

bool
Log::Empty() const
{
    return entries.empty();
}

const string &
Log::LastHash() const
{
    if (entries.empty()) {
        return initialHash;
    } else {
        return entries.back().hash;
    }
}

string
Log::ComputeHash(string lastHash, const LogEntry &entry)
{
    SHA_CTX ctx;
    unsigned char out[SHA_DIGEST_LENGTH];

    SHA1_Init(&ctx);
    
    SHA1_Update(&ctx, lastHash.c_str(), lastHash.size());
    SHA1_Update(&ctx, &entry.viewstamp, sizeof(entry.viewstamp));
    uint64_t x;
    x = entry.request.clientid();
    SHA1_Update(&ctx, &x, sizeof(x));
    x = entry.request.clientreqid();
    SHA1_Update(&ctx, &x, sizeof(x));
    SHA1_Update(&ctx, entry.request.op().c_str(),
                entry.request.op().size());

    SHA1_Final(out, &ctx);

    return string((char *)out, SHA_DIGEST_LENGTH);
}

} // namespace replication
