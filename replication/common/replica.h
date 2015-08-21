// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * replica.h:
 *   interface to different vr protocols
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

#ifndef _COMMON_REPLICA_H_
#define _COMMON_REPLICA_H_


#include "lib/configuration.h"
#include "replication/common/log.h"
#include "replication/common/request.pb.h"
#include "lib/transport.h"
#include "replication/common/viewstamp.h"

namespace replication {
    
class Replica;

enum ReplicaStatus {
    STATUS_NORMAL,
    STATUS_VIEW_CHANGE,
    STATUS_RECOVERING
};

class AppReplica
{
public:
    AppReplica() { };
    virtual ~AppReplica() { };
    // Invoke callback on the leader, with the option to replicate on success 
    virtual void LeaderUpcall(opnum_t opnum, const string &str1, bool &replicate, string &str2) { replicate = true; str2 = str1; };
    // Invoke callback on all replicas
    virtual void ReplicaUpcall(opnum_t opnum, const string &str1, string &str2) { };
    // Invoke call back for unreplicated operations run on only one replica
    virtual void UnloggedUpcall(const string &str1, string &str2) { };
};

class Replica : public TransportReceiver
{
public:
    Replica(const transport::Configuration &config, int myIdx, Transport *transport, AppReplica *app);
    virtual ~Replica();
    
protected:
    void LeaderUpcall(opnum_t opnum, const string &op, bool &replicate, string &res);
    void ReplicaUpcall(opnum_t opnum, const string &op, string &res);
    template<class MSG> void Execute(opnum_t opnum,
                                     const Request & msg,
                                     MSG &reply);
    void UnloggedUpcall(const string &op, string &res);
    template<class MSG> void ExecuteUnlogged(const UnloggedRequest & msg,
                                               MSG &reply);
    
protected:
    transport::Configuration configuration;
    int myIdx;
    Transport *transport;
    AppReplica *app;
    ReplicaStatus status;
};
    
#include "replica-inl.h"

} // namespace replication

#endif  /* _COMMON_REPLICA_H */
