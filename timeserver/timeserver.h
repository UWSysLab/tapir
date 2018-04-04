// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * timeserver/timeserver.h:
 *   Timeserver API
 *
 **********************************************************************/

#ifndef _TIME_SERVER_H_
#define _TIME_SERVER_H_

#include "lib/configuration.h"
#include "replication/common/replica.h"
#if TRANSPORT == UDP
#include "lib/udptransport.h"
#elif TRANSPORT == TCP
#include "lib/tcptransport.h"
#elif TRANSPORT == RDMA
#include "lib/rdmatransport.h"
#endif
#include "replication/vr/replica.h"

#include <string>

using namespace std;

class TimeStampServer : public replication::AppReplica
{
public:
    TimeStampServer();
    ~TimeStampServer();

    void ReplicaUpcall(opnum_t opnum, const string &str1, string &str2);

private:
    long ts;
    string newTimeStamp();
};

#endif /* _TIME_SERVER_H_ */
