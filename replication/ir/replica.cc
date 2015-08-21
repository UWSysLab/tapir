// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * replication/ir/replica.cc:
 *   IR Replica server
 *
 **********************************************************************/

#include "replication/ir/replica.cc"
#include "common/tracer.h"

namespace ir {

using namespace std;
using namespace proto;

IRReplica::IRReplica(const transport::Configuration &configuration, int myIdx,
                     Transport *transport)
    : store(store), configuration(configuration), myIdx(myIdx), transport(transport)
{
    transport->Register(this, configuration, myIdx);
}

IRReplica::~IRReplica() { }

void
IRReplica::ReceiveMessage(const TransportAddress &remote,
                          const string &type, const string &data)
{
    HandleMessage(remote, type, data);
}

void
IRReplica::HandleMessage(const TransportAddress &remote,
                         const string &type, const string &data)
{
    static ProposeInconsistentMessage proposeInconsistent;
    static FinalizeInconsistentMessage finalizeInconsistent;
    static ProposeConsensusMessage proposeConsensus;
    static FinalizeConsensusMessage finalizeConsensus;
    static UnloggedRequestMessage unloggedRequest;

    if (type == proposeInconsistent.GetTypeName()) {
        proposeInconsistent.ParseFromString(data);
        HandleProposeInconsistent(remote, proposeInconsistent);
    } else if (type == finalizeInconsistent.GetTypeName()) {
        finalizeInconsistent.ParseFromString(data);
        HandleFinalizeInconsistent(remote, finalizeInconsistent);
    } else if (type == proposeConsensus.GetTypeName()) {
        proposeConsensus.ParseFromString(data);
        HandleProposeConsensus(remote, proposeConsensus);
    } else if (type == finalizeConsensus.GetTypeName()) {
        finalizeConsensus.ParseFromString(data);
        HandleFinalizeConsensus(remote, finalizeConsensus);
    } else if (type == unloggedRequest.GetTypeName()) {
        unloggedRequest.ParseFromString(data);
        HandleUnlogged(remote, unloggedRequest);
    } else {
        Panic("Received unexpected message type in IR proto: %s",
              type.c_str());
    }
}

void
IRReplica::HandleProposeInconsistent(const TransportAddress &remote,
                                     const ProposeInconsistentMessage &msg)
{
    // 1. Execute

    // 2. Add to record as tentative

    // 3. Return Reply
}
    
void
IRReplica::HandleFinalizeInconsistent(const TransportAddress &remote,
                                      const FinalizeInconsistentMessage &msg)
{
    // 1. Mark as finalized

    // 2. Return Confirm
}

void
IRReplica::HandleProposeConsensus(const TransportAddress &remote,
                                  const ProposeConsensusMessage &msg)
{
    // 1. Execute

    // 2. Add to record as tentative with result

    // 3. Return Reply
}
    
void
IRReplica::HandleFinalizeConsensus(const TransportAddress &remote,
                                   const FinalizeConsensusMessage &msg)
{
    // 1. Mark as finalized with result

    // 2. Return Confirm
}
    
void HandleUnlogged(const TransportAddress &remote,
                    const UnloggedRequestMessage &msg)
{
    // 1. Execute
}
