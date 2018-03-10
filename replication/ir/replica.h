// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * replication/ir/replica.h:
 *   IR Replica server
 *
 **********************************************************************/

#ifndef _IR_REPLICA_H_
#define _IR_REPLICA_H_

#include <memory>

#include "lib/assert.h"
#include "lib/configuration.h"
#include "lib/message.h"
#include "lib/persistent_register.h"
#include "lib/udptransport.h"
#include "replication/common/quorumset.h"
#include "replication/common/replica.h"
#include "replication/ir/ir-proto.pb.h"
#include "replication/ir/record.h"

namespace replication {
namespace ir {


class IRAppReplica
{
public:
    IRAppReplica() { };
    virtual ~IRAppReplica() { };
    // Invoke inconsistent operation, no return value
    virtual void ExecInconsistentUpcall(const string &str1) { };
    // Invoke consensus operation
    virtual void ExecConsensusUpcall(const string &str1, string &str2) { };
    // Invoke unreplicated operation
    virtual void UnloggedUpcall(const string &str1, string &str2) { };
    // Sync
    virtual void Sync(const std::map<opid_t, RecordEntry>& record) { };
    // Merge
    virtual std::map<opid_t, std::string> Merge(
        const std::map<opid_t, std::vector<RecordEntry>> &d,
        const std::map<opid_t, std::vector<RecordEntry>> &u,
        const std::map<opid_t, std::string> &majority_results_in_d) {
        return {};
    };
};


class IRReplica : TransportReceiver
{
public:
    IRReplica(transport::Configuration config, int myIdx,
              Transport *transport, IRAppReplica *app);
    ~IRReplica();

    // Message handlers.
    void ReceiveMessage(const TransportAddress &remote,
                        const std::string &type, const std::string &data);
    void HandleMessage(const TransportAddress &remote,
                       const std::string &type, const std::string &data);
    void HandleProposeInconsistent(const TransportAddress &remote,
                                   const proto::ProposeInconsistentMessage &msg);
    void HandleFinalizeInconsistent(const TransportAddress &remote,
                                    const proto::FinalizeInconsistentMessage &msg);
    void HandleProposeConsensus(const TransportAddress &remote,
                                const proto::ProposeConsensusMessage &msg);
    void HandleFinalizeConsensus(const TransportAddress &remote,
                                 const proto::FinalizeConsensusMessage &msg);
    void HandleDoViewChange(const TransportAddress &remote,
                            const proto::DoViewChangeMessage &msg);
    void HandleStartView(const TransportAddress &remote,
                         const proto::StartViewMessage &msg);
    void HandleUnlogged(const TransportAddress &remote,
                        const proto::UnloggedRequestMessage &msg);

    // Timeout handlers.
    void HandleViewChangeTimeout();

private:
    // Persist `view` and `latest_normal_view` to disk using
    // `persistent_view_info`.
    void PersistViewInfo();

    // Recover `view` and `latest_normal_view` from disk using
    // `persistent_view_info`.
    void RecoverViewInfo();

    // Broadcast DO-VIEW-CHANGE messages to all other replicas with our record
    // included only in the message to the leader.
    void BroadcastDoViewChangeMessages();

    // IrMergeRecords implements Figure 5 of the TAPIR paper.
    Record IrMergeRecords(
        const std::map<int, proto::DoViewChangeMessage> &records);

    transport::Configuration config;
    int myIdx; // Replica index into config.
    Transport *transport;
    IRAppReplica *app;

    ReplicaStatus status;

    // For the view change and recovery protocol, a replica stores its view and
    // latest normal view to disk. We store this info in view and
    // latest_normal_view and use persistent_view_info to persist it to disk.
    view_t view;
    view_t latest_normal_view;
    PersistentRegister persistent_view_info;

    Record record;
    std::unique_ptr<Timeout> view_change_timeout;

    // The leader of a view-change waits to receive a quorum of DO-VIEW-CHANGE
    // messages before merging and syncing and sending out START-VIEW messages.
    // do_view_change_quorum is used to wait for this quorum.
    //
    // TODO: Garbage collect old view change quorums. Once we've entered view
    // v, we should be able to garbage collect all quorums for views less than
    // v.
    QuorumSet<view_t, proto::DoViewChangeMessage> do_view_change_quorum;
};

} // namespace ir
} // namespace replication

#endif /* _IR_REPLICA_H_ */
