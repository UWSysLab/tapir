// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * common/timestamp.h
 *   A transaction timestamp
 *
 **********************************************************************/

#ifndef _TIMESTAMP_H_
#define _TIMESTAMP_H_

#include "lib/assert.h"
#include "lib/message.h"
#include "store/common/common-proto.pb.h"

class Timestamp
{

public:
    Timestamp() : timestamp(0), id(0) { };
    Timestamp(uint64_t t) : timestamp(t), id(0) { };
    Timestamp(uint64_t t, uint64_t i) : timestamp(t), id(i) { };
    Timestamp(const TimestampMessage &msg) : timestamp(msg.timestamp()), id(msg.id()) { };
    ~Timestamp() { };
    void operator= (const Timestamp &t);
    bool operator== (const Timestamp &t) const;
    bool operator!= (const Timestamp &t) const;
    bool operator> (const Timestamp &t) const;
    bool operator< (const Timestamp &t) const;
    bool operator>= (const Timestamp &t) const;
    bool operator<= (const Timestamp &t) const;
    bool isValid() const;
    uint64_t getID() const { return id; };
    uint64_t getTimestamp() const { return timestamp; };
    void setTimestamp(uint64_t t) { timestamp = t; };  
    void serialize(TimestampMessage *msg) const;

private:
	uint64_t timestamp;
	uint64_t id;
};

#endif  /* _TIMESTAMP_H_ */
