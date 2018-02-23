// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * replication/ir/replica.cc:
 *   IR Replica server
 *
 **********************************************************************/

#include "replication/ir/replica.h"

namespace replication {
namespace ir {

using namespace std;
using namespace proto;

IRReplica::IRReplica(transport::Configuration config, int myIdx,
                     Transport *transport, IRAppReplica *app) :
    view(0),
    myIdx(myIdx),
    transport(transport),
    app(app)
{
    transport->Register(this, config, myIdx);
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
    ProposeInconsistentMessage proposeInconsistent;
    FinalizeInconsistentMessage finalizeInconsistent;
    ProposeConsensusMessage proposeConsensus;
    FinalizeConsensusMessage finalizeConsensus;
    UnloggedRequestMessage unloggedRequest;

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
    uint64_t clientid = msg.req().clientid();
    uint64_t clientreqid = msg.req().clientreqid();

    Debug("%lu:%lu Received inconsistent op: %s", clientid, clientreqid, (char *)msg.req().op().c_str());
    
    opid_t opid = make_pair(clientid, clientreqid);
    
    // Check record if we've already handled this request
    RecordEntry *entry = record.Find(opid);
    ReplyInconsistentMessage reply;
    if (entry != NULL) {
        // If we already have this op in our record, then just return it
        reply.set_view(entry->view);
        reply.set_replicaidx(myIdx);
        reply.mutable_opid()->set_clientid(clientid);
        reply.mutable_opid()->set_clientreqid(clientreqid);
    } else {
        // Otherwise, put it in our record as tentative
        record.Add(view, opid, msg.req(), RECORD_STATE_TENTATIVE);
    
        // 3. Return Reply
        reply.set_view(view);
        reply.set_replicaidx(myIdx);
        reply.mutable_opid()->set_clientid(clientid);
        reply.mutable_opid()->set_clientreqid(clientreqid);
    }

    // Send the reply
    transport->SendMessage(this, remote, reply);
    
}
    
void
IRReplica::HandleFinalizeInconsistent(const TransportAddress &remote,
                                      const FinalizeInconsistentMessage &msg)
{
    uint64_t clientid = msg.opid().clientid();
    uint64_t clientreqid = msg.opid().clientreqid();

    Debug("%lu:%lu Received finalize inconsistent op", clientid, clientreqid);
    
    opid_t opid = make_pair(clientid, clientreqid);
    
    // Check record for the request
    RecordEntry *entry = record.Find(opid);    
    if (entry != NULL && entry->state == RECORD_STATE_TENTATIVE) {
        // Mark entry as finalized
        record.SetStatus(opid, RECORD_STATE_FINALIZED);

        // Execute the operation
        app->ExecInconsistentUpcall(entry->request.op());

        // Send the reply
        ConfirmMessage reply;
        reply.set_view(view);
        reply.set_replicaidx(myIdx);
        *reply.mutable_opid() = msg.opid();

        transport->SendMessage(this, remote, reply);
    } else {
        // Ignore?
    }    
}

void
IRReplica::HandleProposeConsensus(const TransportAddress &remote,
                                  const ProposeConsensusMessage &msg)
{
    uint64_t clientid = msg.req().clientid();
    uint64_t clientreqid = msg.req().clientreqid();

    Debug("%lu:%lu Received consensus op: %s", clientid, clientreqid, (char *)msg.req().op().c_str());
    
    opid_t opid = make_pair(clientid, clientreqid);
    
    // Check record if we've already handled this request
    RecordEntry *entry = record.Find(opid);
    ReplyConsensusMessage reply;
    if (entry != NULL) {
        // If we already have this op in our record, then just return it
        reply.set_view(entry->view);
        reply.set_replicaidx(myIdx);
        reply.mutable_opid()->set_clientid(clientid);
        reply.mutable_opid()->set_clientreqid(clientreqid);
        reply.set_result(entry->result);
    } else {
        // Execute op
        string result;

        app->ExecConsensusUpcall(msg.req().op(), result);

        // Put it in our record as tentative
        record.Add(view, opid, msg.req(), RECORD_STATE_TENTATIVE, result);

        
        // 3. Return Reply
        reply.set_view(view);
        reply.set_replicaidx(myIdx);
        reply.mutable_opid()->set_clientid(clientid);
        reply.mutable_opid()->set_clientreqid(clientreqid);
        reply.set_result(result);
    }

    // Send the reply
    transport->SendMessage(this, remote, reply);
}
    
void
IRReplica::HandleFinalizeConsensus(const TransportAddress &remote,
                                   const FinalizeConsensusMessage &msg)
{
    uint64_t clientid = msg.opid().clientid();
    uint64_t clientreqid = msg.opid().clientreqid();
    
    Debug("%lu:%lu Received finalize consensus op", clientid, clientreqid);

    opid_t opid = make_pair(clientid, clientreqid);
    
    // Check record for the request
    RecordEntry *entry = record.Find(opid);    
    if (entry != NULL) {
        // Mark entry as finalized
        record.SetStatus(opid, RECORD_STATE_FINALIZED);

        if (msg.result() != entry->result) {
            // Update the result
            entry->result = msg.result();
        }

        // Send the reply
        ConfirmMessage reply;
        reply.set_view(view);
        reply.set_replicaidx(myIdx);
        *reply.mutable_opid() = msg.opid();

        if (!transport->SendMessage(this, remote, reply)) {
            Warning("Failed to send reply message");
        }
    } else {
        // Ignore?
        Warning("Finalize request for unknown consensus operation");
    }
}
    
void
IRReplica::HandleUnlogged(const TransportAddress &remote,
                    const UnloggedRequestMessage &msg)
{
    UnloggedReplyMessage reply;
    string res;
    
    Debug("Received unlogged request %s", (char *)msg.req().op().c_str());

    app->UnloggedUpcall(msg.req().op(), res);
    reply.set_reply(res);
    reply.set_clientreqid(msg.req().clientreqid());    
    if (!(transport->SendMessage(this, remote, reply)))
        Warning("Failed to send reply message");
}

} // namespace ir
} // namespace replication
