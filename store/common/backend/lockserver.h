// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * spanstore/lockserver.h:
 *   Simple multi-reader, single-writer lock server.
 *
 **********************************************************************/

#ifndef _LOCK_SERVER_H_
#define _LOCK_SERVER_H_

#include "paxos-lib/lib/assert.h"
#include "paxos-lib/lib/message.h"
#include <sys/time.h>
#include <map>
#include <queue>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>

namespace spanstore {

#define LOCK_WAIT_TIMEOUT 5000

class LockServer
{

public:
    LockServer();
    ~LockServer();

    bool lockForRead(const std::string &lock, uint64_t requester);
    bool lockForWrite(const std::string &lock, uint64_t requester);
    void releaseForRead(const std::string &lock, uint64_t holder);
    void releaseForWrite(const std::string &lock, uint64_t holder);

private:
    enum LockState {
        UNLOCKED,
        LOCKED_FOR_READ,
        LOCKED_FOR_WRITE,
        LOCKED_FOR_READ_WRITE
    };

    struct Waiter {
        bool write;
        struct timeval waitTime;

        Waiter() {write = false;}
        Waiter(bool w) {
            gettimeofday(&waitTime, NULL);
            write = w;
        }

        bool checkTimeout(const struct timeval &now);
    };

    struct Lock {
        LockState state;
        std::unordered_set<uint64_t> holders;
        std::queue<uint64_t> waitQ;
        std::map<uint64_t, Waiter> waiters;

        Lock() {
            state = UNLOCKED;
        };
        void waitForLock(uint64_t requester, bool write);
        bool tryAcquireLock(uint64_t requester, bool write);
        bool isWriteNext();
    };

    /* Global store which keep key -> (timestamp, value) list. */
    std::unordered_map<std::string, Lock> locks;

    uint64_t readers;
    uint64_t writers;
};

} // namespace spanstore

#endif /* _LOCK_SERVER_H_ */
