// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/tapirstore/server.cc:
 *   Implementation of a single transactional key-value server.
 *
 * Copyright 2015 Irene Zhang <iyzhang@cs.washington.edu>
 *                Naveen Kr. Sharma <naveenks@cs.washington.edu>
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

#include "store/tapirstore/server.h"

namespace tapirstore {

using namespace std;
using namespace proto;

Server::Server(bool linearizable)
{
    store = new Store(linearizable);
}

Server::~Server()
{
    delete store;
}

void
Server::ExecInconsistentUpcall(const string &str1)
{
    Debug("Received Inconsistent Request: %s",  str1.c_str());

    Request request;

    request.ParseFromString(str1);

    switch (request.op()) {
    case tapirstore::proto::Request::COMMIT:
        store->Commit(request.txnid(), request.commit().timestamp());
        break;
    case tapirstore::proto::Request::ABORT:
        store->Abort(request.txnid(), Transaction(request.abort().txn()));
        break;
    default:
        Panic("Unrecognized inconsisternt operation.");
    }
}

void
Server::ExecConsensusUpcall(const string &str1, string &str2)
{
    Debug("Received Consensus Request: %s", str1.c_str());

    Request request;
    Reply reply;
    int status;
    Timestamp proposed;

    request.ParseFromString(str1);

    switch (request.op()) {
    case tapirstore::proto::Request::PREPARE:
        status = store->Prepare(request.txnid(),
                                Transaction(request.prepare().txn()),
                                Timestamp(request.prepare().timestamp()),
                                proposed);
        reply.set_status(status);
        if (proposed.isValid()) {
            proposed.serialize(reply.mutable_timestamp());
        }
        reply.SerializeToString(&str2);
        break;
    default:
        Panic("Unrecognized consensus operation.");
    }

}

void
Server::UnloggedUpcall(const string &str1, string &str2)
{
    Debug("Received Consensus Request: %s", str1.c_str());

    Request request;
    Reply reply;
    int status;

    request.ParseFromString(str1);

    switch (request.op()) {
    case tapirstore::proto::Request::GET:
        if (request.get().has_timestamp()) {
            pair<Timestamp, string> val;
            status = store->Get(request.txnid(), request.get().key(),
                               request.get().timestamp(), val);
            if (status == 0) {
                reply.set_value(val.second);
            }
        } else {
            pair<Timestamp, string> val;
            status = store->Get(request.txnid(), request.get().key(), val);
            if (status == 0) {
                reply.set_value(val.second);
                val.first.serialize(reply.mutable_timestamp());
            }
        }
        reply.set_status(status);
        reply.SerializeToString(&str2);
        break;
    default:
        Panic("Unrecognized Unlogged request.");
    }
}

void
Server::Sync(const std::map<opid_t, RecordEntry>& record)
{
    Panic("Unimplemented!");
}

std::map<opid_t, std::string>
Server::Merge(const std::map<opid_t, std::vector<RecordEntry>> &d,
              const std::map<opid_t, std::vector<RecordEntry>> &u,
              const std::map<opid_t, std::string> &majority_results_in_d)
{
    Panic("Unimplemented!");
}

void
Server::Load(const string &key, const string &value, const Timestamp timestamp)
{
    store->Load(key, value, timestamp);
}

} // namespace tapirstore


int
main(int argc, char **argv)
{
    int index = -1;
    unsigned int myShard = 0, maxShard = 1, nKeys = 1;
    const char *configPath = NULL;
    const char *keyPath = NULL;
    bool linearizable = true;

    // Parse arguments
    int opt;
    while ((opt = getopt(argc, argv, "c:i:m:e:s:f:n:N:k:")) != -1) {
        switch (opt) {
        case 'c':
            configPath = optarg;
            break;

        case 'i':
        {
            char *strtolPtr;
            index = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0') || (index < 0))
            {
                fprintf(stderr, "option -i requires a numeric arg\n");
            }
            break;
        }

        case 'm':
        {
            if (strcasecmp(optarg, "txn-l") == 0) {
                linearizable = true;
            } else if (strcasecmp(optarg, "txn-s") == 0) {
                linearizable = false;
            } else {
                fprintf(stderr, "unknown mode '%s'\n", optarg);
            }
            break;
        }

        case 'k':
        {
            char *strtolPtr;
            nKeys = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0'))
            {
                fprintf(stderr, "option -e requires a numeric arg\n");
            }
            break;
        }

        case 'n':
        {
            char *strtolPtr;
            myShard = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0'))
            {
                fprintf(stderr, "option -e requires a numeric arg\n");
            }
            break;
        }

        case 'N':
        {
            char *strtolPtr;
            maxShard = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0'))
            {
                fprintf(stderr, "option -e requires a numeric arg\n");
            }
            break;
        }

        case 'f':   // Load keys from file
        {
            keyPath = optarg;
            break;
        }

        default:
            fprintf(stderr, "Unknown argument %s\n", argv[optind]);
        }
    }

    if (!configPath) {
        fprintf(stderr, "option -c is required\n");
    }

    if (index == -1) {
        fprintf(stderr, "option -i is required\n");
    }

    // Load configuration
    std::ifstream configStream(configPath);
    if (configStream.fail()) {
        fprintf(stderr, "unable to read configuration file: %s\n", configPath);
    }
    transport::Configuration config(configStream);

    if (index >= config.n) {
        fprintf(stderr, "replica index %d is out of bounds; "
                "only %d replicas defined\n", index, config.n);
    }

    UDPTransport transport(0.0, 0.0, 0);

    tapirstore::Server server(linearizable);

    replication::ir::IRReplica replica(config, index, &transport, &server);

    if (keyPath) {
        string key;
        std::ifstream in;
        in.open(keyPath);
        if (!in) {
            fprintf(stderr, "Could not read keys from: %s\n", keyPath);
            exit(0);
        }

        for (unsigned int i = 0; i < nKeys; i++) {
            getline(in, key);

            uint64_t hash = 5381;
            const char* str = key.c_str();
            for (unsigned int j = 0; j < key.length(); j++) {
                hash = ((hash << 5) + hash) + (uint64_t)str[j];
            }

            if (hash % maxShard == myShard) {
                server.Load(key, "null", Timestamp());
            }
        }
        in.close();
    }

    transport.Run();

    return 0;
}
