// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * client.cc:
 *   interface to replication client stubs
 *
 * Copyright 2013 Dan R. K. Ports  <drkp@cs.washington.edu>
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

#include "replication/common/client.h"
#include "replication/common/request.pb.h"
#include "lib/message.h"
#include "lib/transport.h"

#include <random>

namespace replication {

std::string ErrorCodeToString(ErrorCode err) {
    switch (err) {
        case ErrorCode::TIMEOUT:
            return "TIMEOUT";
        case ErrorCode::MISMATCHED_CONSENSUS_VIEWS:
            return "MISMATCHED_CONSENSUS_VIEWS";
        default:
            Assert(false);
            return "";
    }
}

Client::Client(const transport::Configuration &config, Transport *transport,
               uint64_t clientid)
    : config(config), transport(transport)
{
    this->clientid = clientid;

    // Randomly generate a client ID
    // This is surely not the fastest way to get a random 64-bit int,
    // but it should be fine for this purpose.
    while (this->clientid == 0) {
        std::random_device rd;
        std::mt19937_64 gen(rd());
        std::uniform_int_distribution<uint64_t> dis;
        this->clientid = dis(gen);
        Debug("VRClient ID: %lu", this->clientid);
    }

    transport->Register(this, config, -1);
}

Client::~Client()
{

}

void
Client::ReceiveMessage(const TransportAddress &remote,
                       const string &type, const string &data)
{
    Panic("Received unexpected message type: %s",
          type.c_str());
}

} // namespace replication
