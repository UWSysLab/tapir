// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * timeserver/timeserver.h:
 *   Timeserver API
 *
 **********************************************************************/

#ifndef _TIME_SERVER_H_
#define _TIME_SERVER_H_

#include "paxos-lib/lib/configuration.h"
#include "paxos-lib/common/replica.h"
#include "paxos-lib/lib/udptransport.h"
#include "paxos-lib/vr/replica.h"

#include <string>

using namespace std;

class TimeStampServer : public specpaxos::AppReplica
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
