// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * replica.cc:
 *   common functions for replica implementation regardless of
 *   replication protocol
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

#include "replication/common/log.h"
#include "replication/common/replica.h"

#include "lib/message.h"

#include <stdlib.h>

namespace replication {
    
Replica::Replica(const transport::Configuration &configuration, int myIdx,
                 Transport *transport, AppReplica *app)
    : configuration(configuration), myIdx(myIdx),
      transport(transport), app(app)
{
    transport->Register(this, configuration, myIdx);
}

Replica::~Replica()
{
    
}

void
Replica::LeaderUpcall(opnum_t opnum, const string &op, bool &replicate, string &res)
{
    Debug("Making leader upcall for operation %s", op.c_str());
    app->LeaderUpcall(opnum, op, replicate, res);
    Debug("Upcall result: %s %s", replicate ? "yes":"no", res.c_str());
}

void
Replica::ReplicaUpcall(opnum_t opnum, const string &op, string &res)
{
    Debug("Making upcall for operation %s", op.c_str());
    app->ReplicaUpcall(opnum, op, res);
    
    Debug("Upcall result: %s", res.c_str());
}

void
Replica::UnloggedUpcall(const string &op, string &res)
{
    app->UnloggedUpcall(op, res);
}

} // namespace replication
