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

#ifndef _IR_RECORD_H_
#define _IR_RECORD_H_

#include "replication/common/request.pb.h"
#include "lib/assert.h"
#include "lib/message.h"
#include "lib/transport.h"
#include "replication/common/viewstamp.h"

#include <map>
#include <string>
#include <utility>

namespace replication {
namespace ir {

enum RecordEntryState {
    RECORD_STATE_TENTATIVE,
    RECORD_STATE_FINALIZED
};

typedef std::pair<uint64_t, uint64_t> opid_t;
    
struct RecordEntry
{
    view_t view;
    opid_t opid;
    RecordEntryState state;
    Request request;
    std::string result;
    
    RecordEntry() { result = ""; }
    RecordEntry(const RecordEntry &x)
        : view(x.view), opid(x.opid), state(x.state), request(x.request),
          result(x.result) { }
    RecordEntry(view_t view, opid_t opid, RecordEntryState state,
                const Request &request, const std::string &result)
        : view(view), opid(opid), state(state), request(request),
          result(result) { }
    virtual ~RecordEntry() { }
};

class Record
{
public:
    Record() {};
    RecordEntry & Add(view_t view, opid_t opid, const Request &request, RecordEntryState state);
    RecordEntry & Add(view_t view, opid_t opid, const Request &request, RecordEntryState state, const std::string &result);
    RecordEntry * Find(opid_t opid);
    bool SetStatus(opid_t opid, RecordEntryState state);
    bool SetResult(opid_t opid, const std::string &result);
    bool SetRequest(opid_t opid, const Request &req);
    void Remove(opid_t opid);
    bool Empty() const;

private:
    std::map<opid_t, RecordEntry> entries;

};

}      // namespace ir
}      // namespace replication
#endif  /* _IR_RECORD_H_ */
