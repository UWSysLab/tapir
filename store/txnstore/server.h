// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * spanstore/replica.h:
 *   A single SpanStore server replica.
 *
 **********************************************************************/

#ifndef _SPAN_SERVER_H_
#define _SPAN_SERVER_H_

#include "paxos-lib/lib/configuration.h"
#include "paxos-lib/common/replica.h"
#include "paxos-lib/lib/udptransport.h"
#include "paxos-lib/vr/replica.h"
#include "common/truetime.h"
#include "common/txnstore.h"
#include "spanstore/occstore.h"
#include "spanstore/lockstore.h"
#include "spanstore/span-proto.pb.h"

namespace spanstore {

enum Mode {
    MODE_UNKNOWN,
    MODE_OCC,
    MODE_LOCK,
    MODE_SPAN_OCC,
    MODE_SPAN_LOCK
};

class Server : public specpaxos::AppReplica
{
public:
    Server(Mode mode, uint64_t skew, uint64_t error);
    virtual ~Server();

    virtual void LeaderUpcall(opnum_t opnum, const string &str1, bool &replicate, string &str2);
    virtual void ReplicaUpcall(opnum_t opnum, const string &str1, string &str2);
    virtual void UnloggedUpcall(const string &str1, string &str2);
    void Load(const string &key, const string &value, const Timestamp timestamp);

private:
    Mode mode;
    TxnStore *store;
    TrueTime timeServer;
};

} // namespace spanstore

#endif /* _SPAN_SERVER_H_ */
