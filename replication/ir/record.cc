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

#include "replication/ir/record.h"

#include <utility>

#include "lib/assert.h"

namespace replication {
namespace ir {

Record::Record(const proto::RecordProto &record_proto) {
    for (const proto::RecordEntryProto &entry_proto : record_proto.entry()) {
        const view_t view = entry_proto.view();
        const opid_t opid = std::make_pair(entry_proto.opid().clientid(),
                                     entry_proto.opid().clientreqid());
        Request request;
        request.set_op(entry_proto.op());
        request.set_clientid(entry_proto.opid().clientid());
        request.set_clientreqid(entry_proto.opid().clientreqid());
        proto::RecordEntryState state = entry_proto.state();
        proto::RecordEntryType type = entry_proto.type();
        const std::string& result = entry_proto.result();
        Add(view, opid, request, state, type, result);
    }
}

RecordEntry &
Record::Add(const RecordEntry& entry) {
    // Make sure this isn't a duplicate
    ASSERT(entries.count(entry.opid) == 0);
    entries[entry.opid] = entry;
    return entries[entry.opid];
}

RecordEntry &
Record::Add(view_t view, opid_t opid, const Request &request,
            proto::RecordEntryState state, proto::RecordEntryType type)
{
    return Add(RecordEntry(view, opid, state, type, request, ""));
}

RecordEntry &
Record::Add(view_t view, opid_t opid, const Request &request,
            proto::RecordEntryState state, proto::RecordEntryType type,
            const string &result)
{
    RecordEntry &entry = Add(view, opid, request, state, type);
    entry.result = result;
    return entries[opid];
}

// This really ought to be const
RecordEntry *
Record::Find(opid_t opid)
{
    if (entries.empty() || entries.count(opid) == 0) {
        return NULL;
    }

    RecordEntry *entry = &entries[opid];
    ASSERT(entry->opid == opid);
    return entry;
}


bool
Record::SetStatus(opid_t op, proto::RecordEntryState state)
{
    RecordEntry *entry = Find(op);
    if (entry == NULL) {
        return false;
    }

    entry->state = state;
    return true;
}

bool
Record::SetResult(opid_t op, const string &result)
{
    RecordEntry *entry = Find(op);
    if (entry == NULL) {
        return false;
    }

    entry->result = result;
    return true;
}

bool
Record::SetRequest(opid_t op, const Request &req)
{
    RecordEntry *entry = Find(op);
    if (entry == NULL) {
        return false;
    }

    entry->request = req;
    return true;
}

void
Record::Remove(opid_t opid)
{
    entries.erase(opid);
}

bool
Record::Empty() const
{
    return entries.empty();
}

void
Record::ToProto(proto::RecordProto *proto) const
{
    for (const std::pair<const opid_t, RecordEntry> &p : entries) {
        const RecordEntry &entry = p.second;
        proto::RecordEntryProto *entry_proto = proto->add_entry();

        entry_proto->set_view(entry.view);
        entry_proto->mutable_opid()->set_clientid(entry.opid.first);
        entry_proto->mutable_opid()->set_clientreqid(entry.opid.second);
        entry_proto->set_state(entry.state);
        entry_proto->set_type(entry.type);
        entry_proto->set_op(entry.request.op());
        entry_proto->set_result(entry.result);
    }
}

const std::map<opid_t, RecordEntry> &Record::Entries() const {
    return entries;
}

} // namespace ir
} // namespace replication
