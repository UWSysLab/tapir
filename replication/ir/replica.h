// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * replication/ir/replica.h:
 *   IR Replica server
 *
 **********************************************************************/

#ifndef _IR_REPLICA_H_
#define _IR_REPLICA_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "lib/udptransport.h"
#include "lib/configuration.h"

namespace ir {

class AppReplica
{
public:
    AppReplica() { };
    virtual ~AppReplica() { };
    // Invoke inconsistent operation, no return value
    virtual void ExecInconsistentUpcall(const string &str1);
    // Invoke consensus operation
    virtual void ReplicaUpcall(const string &str1, string &str2) { };
    // Invoke call back for unreplicated operations run on only one replica
    virtual void UnloggedUpcall(const string &str1, string &str2) { };
};

    
class IRReplica : TransportReceiver
{
private:

    view_t view;

    // Index of 'this' replica, and handle to transport layer.
    int myIdx;
    Transport *transport;

public:
    IRReplica(const specpaxos::Configuration &configuration, int myIdx,
              Transport *transport);
    ~IRReplica();

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
    void HandleUnlogged(const TransportAddress &remote,
                        const proto::UnloggedRequestMessage &msg);

    
    
    void Load(const std::string &key, const std::string &value, const Timestamp &timestamp);

};

} // namespace ir

#endif /* _IR_REPLICA_H_ */
