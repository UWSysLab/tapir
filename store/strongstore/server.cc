// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * store/strongstore/server.cc:
 *   Implementation of a single transactional key-value server with strong consistency.
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

#include "store/strongstore/server.h"

namespace strongstore {

using namespace std;
using namespace proto;

Server::Server(Mode mode, uint64_t skew, uint64_t error) : mode(mode)
{
    timeServer = TrueTime(skew, error);

    switch (mode) {
    case MODE_LOCK:
    case MODE_SPAN_LOCK:
        store = new strongstore::LockStore();
        break;
    case MODE_OCC:
    case MODE_SPAN_OCC:
        store = new strongstore::OCCStore();
        break;
    default:
        NOT_REACHABLE();
    }
}

Server::~Server()
{
    delete store;
}

void
Server::LeaderUpcall(opnum_t opnum, const string &str1, bool &replicate, string &str2)
{
    Debug("Received LeaderUpcall: %lu %s", opnum, str1.c_str());

    Request request;
    Reply reply;
    int status;
    
    request.ParseFromString(str1);

    switch (request.op()) {
    case strongstore::proto::Request::GET:
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
                reply.set_timestamp(val.first.getTimestamp());
            }
        }
        replicate = false;
        reply.set_status(status);
        reply.SerializeToString(&str2);
        break;
    case strongstore::proto::Request::PREPARE:
        // Prepare is the only case that is conditionally run at the leader
        status = store->Prepare(request.txnid(),
                                Transaction(request.prepare().txn()));

        // if prepared, then replicate result
        if (status == 0) {
            replicate = true;
            // get a prepare timestamp and send along to replicas
            if (mode == MODE_SPAN_LOCK || mode == MODE_SPAN_OCC) {
                request.mutable_prepare()->set_timestamp(timeServer.GetTime());
            }
            request.SerializeToString(&str2);
        } else {
            // if abort, don't replicate
            replicate = false;
            reply.set_status(status);
            reply.SerializeToString(&str2);
        }
        break;
    case strongstore::proto::Request::COMMIT:
        replicate = true;
        str2 = str1;
        break;
    case strongstore::proto::Request::ABORT:
        replicate = true;
        str2 = str1;
        break;
    default:
        Panic("Unrecognized operation.");
    }
}

/* Gets called when a command is issued using client.Invoke(...) to this
 * replica group. 
 * opnum is the operation number.
 * str1 is the request string passed by the client.
 * str2 is the reply which will be sent back to the client.
 */
void
Server::ReplicaUpcall(opnum_t opnum,
              const string &str1,
              string &str2)
{
    Debug("Received Upcall: %lu %s", opnum, str1.c_str());
    Request request;
    Reply reply;
    int status = 0;
    
    request.ParseFromString(str1);

    switch (request.op()) {
    case strongstore::proto::Request::GET:
        return;
    case strongstore::proto::Request::PREPARE:
        // get a prepare timestamp and return to client
        store->Prepare(request.txnid(),
                       Transaction(request.prepare().txn()));
        if (mode == MODE_SPAN_LOCK || mode == MODE_SPAN_OCC) {
            reply.set_timestamp(request.prepare().timestamp());
        }
        break;
    case strongstore::proto::Request::COMMIT:
        store->Commit(request.txnid(), request.commit().timestamp());
        break;
    case strongstore::proto::Request::ABORT:
        store->Abort(request.txnid(), Transaction(request.abort().txn()));
        break;
    default:
        Panic("Unrecognized operation.");
    }
    reply.set_status(status);
    reply.SerializeToString(&str2);
}

void
Server::UnloggedUpcall(const string &str1, string &str2)
{
    Request request;
    Reply reply;
    int status;
    
    request.ParseFromString(str1);

    ASSERT(request.op() == strongstore::proto::Request::GET);

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
            reply.set_timestamp(val.first.getTimestamp());
        }
    }
    
    reply.set_status(status);
    reply.SerializeToString(&str2);
}

void
Server::Load(const string &key, const string &value, const Timestamp timestamp)
{
    store->Load(key, value, timestamp);
}

} // namespace strongstore

int
main(int argc, char **argv)
{
    int index = -1;
    unsigned int myShard=0, maxShard=1, nKeys=1;
    const char *configPath = NULL;
    const char *keyPath = NULL;
    int64_t skew = 0, error = 0;
    strongstore::Mode mode;

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
            if (strcasecmp(optarg, "lock") == 0) {
                mode = strongstore::MODE_LOCK;
            } else if (strcasecmp(optarg, "occ") == 0) {
                mode = strongstore::MODE_OCC;
            } else if (strcasecmp(optarg, "span-lock") == 0) {
                mode = strongstore::MODE_SPAN_LOCK;
            } else if (strcasecmp(optarg, "span-occ") == 0) {
                mode = strongstore::MODE_SPAN_OCC;
            } else {
                fprintf(stderr, "unknown mode '%s'\n", optarg);
            }
            break;
        }

        case 's':
        {
            char *strtolPtr;
            skew = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0') || (skew < 0))
            {
                fprintf(stderr, "option -s requires a numeric arg\n");
            }
            break;
        }

        case 'e':
        {
            char *strtolPtr;
            error = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0') || (error < 0))
            {
                fprintf(stderr, "option -e requires a numeric arg\n");
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
            if ((*optarg == '\0') || (*strtolPtr != '\0') || (maxShard <= 0))
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

    if (mode == strongstore::MODE_UNKNOWN) {
        fprintf(stderr, "option -m is required\n");
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

    strongstore::Server server(mode, skew, error);
    replication::vr::VRReplica replica(config, index, &transport, 1, &server);
    
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
