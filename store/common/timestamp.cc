// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * common/timestamp.cc:
 *   A transaction timestamp implementation
 *
 **********************************************************************/

#include "store/common/timestamp.h"

void
Timestamp::operator=(const Timestamp &t)
{
    timestamp = t.timestamp;
    id = t.id;
}

bool
Timestamp::operator==(const Timestamp &t) const
{
    return timestamp == t.timestamp && id == t.id;
}

bool
Timestamp::operator!=(const Timestamp &t) const
{
    return timestamp != t.timestamp || id != t.id;
}

bool
Timestamp::operator>(const Timestamp &t) const
{
    return (timestamp == t.timestamp) ? id > t.id : timestamp > t.timestamp; 
}

bool
Timestamp::operator<(const Timestamp &t) const
{
    return (timestamp == t.timestamp) ? id < t.id : timestamp < t.timestamp; 
}

bool
Timestamp::operator>=(const Timestamp &t) const
{
    return (timestamp == t.timestamp) ? id >= t.id : timestamp >= t.timestamp; 
}

bool
Timestamp::operator<=(const Timestamp &t) const
{
    return (timestamp == t.timestamp) ? id <= t.id : timestamp <= t.timestamp; 
}

bool
Timestamp::isValid() const
{
    return timestamp > 0 && id > 0;
}

void
Timestamp::serialize(TimestampMessage *msg) const
{
    msg->set_timestamp(timestamp);
    msg->set_id(id);
}
