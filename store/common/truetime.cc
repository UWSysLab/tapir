// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * common/truetime.cc:
 *   A simulated TrueTime module
 *
 **********************************************************************/

#include "store/common/truetime.h"

TrueTime::TrueTime() {
    simError = 0;
    simSkew = 0;
}

TrueTime::TrueTime(uint64_t skew, uint64_t errorBound)
{
    simError = errorBound;
    if (skew == 0) {
        simSkew = 0;
    } else {
        struct timeval t1;
        gettimeofday(&t1, NULL);
        srand(t1.tv_sec + t1.tv_usec);
        uint64_t r = rand();
        simSkew = (r % skew) - (skew / 2);
    }

    Debug("TrueTime variance: skew=%lu error=%lu", simSkew, simError);
}    

uint64_t
TrueTime::GetTime()
{
    struct timeval now;
    uint64_t timestamp;

    gettimeofday(&now, NULL);

    now.tv_usec += simSkew;
    if (now.tv_usec > 999999) {
        now.tv_usec -= 1000000;
        now.tv_sec++;
    } else if (now.tv_usec < 0) {
        now.tv_usec += 1000000;
        now.tv_sec--;
    }

    timestamp = ((uint64_t)now.tv_sec << 32) | (uint64_t) (now.tv_usec);

    Debug("Time: %lx %lx %lx", now.tv_sec,now.tv_usec,timestamp);

    return timestamp;
}

void
TrueTime::GetTimeAndError(uint64_t &time, uint64_t &error)
{
   time = GetTime();
   error = simError;
}
