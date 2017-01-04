// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * common/truetime.h
 *   A simulated TrueTime module
 *
 **********************************************************************/

#ifndef _TRUETIME_H_
#define _TRUETIME_H_

#include "lib/message.h"

#include <sys/time.h>
#include <cstdlib>

class TrueTime
{
 public:
    TrueTime();
    TrueTime(uint64_t skew, uint64_t errorBound);
    ~TrueTime() { };
   
    uint64_t GetTime();
    void GetTimeAndError(uint64_t &time, uint64_t &error);

private:
	uint64_t simError;
	uint64_t simSkew;
};

#endif  /* _TRUETIME_H_ */
