// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * lockserver/server.cc:
 *   A lockserver replica.
 *
 * Copyright 2015 Naveen Kr. Sharma <naveenks@cs.washington.edu>
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

#include "lockserver/server.h"

int
main(int argc, char **argv)
{
    int index = -1;
    const char *configPath = NULL;

    // Parse arguments
    int opt;
    char *strtolPtr;
    while ((opt = getopt(argc, argv, "c:i:")) != -1) {
        switch (opt) {
        case 'c':
            configPath = optarg;
            break;
            
        case 'i':
            index = strtol(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0') || (index < 0)) {
                fprintf(stderr, "option -i requires a numeric arg\n");
            }
            break;
        
        default:
            fprintf(stderr, "Unknown argument %s\n", argv[optind]);
        }
    }

    if (!configPath) {
        fprintf(stderr, "option -c is required\n");
        return EXIT_FAILURE;
    }

    if (index == -1) {
        fprintf(stderr, "option -i is required\n");
        return EXIT_FAILURE;
    }

    // Load configuration
    std::ifstream configStream(configPath);
    if (configStream.fail()) {
        fprintf(stderr, "unable to read configuration file: %s\n", configPath);
        return EXIT_FAILURE;
    }
    transport::Configuration config(configStream);

    if (index >= config.n) {
        fprintf(stderr, "replica index %d is out of bounds; "
                "only %d replicas defined\n", index, config.n);
        return EXIT_FAILURE;
    }

    UDPTransport transport(0.0, 0.0, 0);

    lockserver::LockServer server;
    replication::ir::IRReplica replica(config, index, &transport, &server);
    
    transport.Run();

    return EXIT_SUCCESS;
}

namespace lockserver {

using namespace proto;

LockServer::LockServer() { }
LockServer::~LockServer() { }

void
LockServer::ExecInconsistentUpcall(const string &str1)
{
    Debug("ExecInconsistent: %s\n", str1.c_str());

    Request request;

    request.ParseFromString(str1);
    string key = request.key();
    uint64_t client_id = request.clientid();

    if (request.type()) { // Lock operation.
        Warning("Lock operation being sent as Inconsistent. Ignored.");
    } else {
        if (locks.find(key) != locks.end()) {
            if (client_id == locks[key]) {
                Debug("Releasing lock %lu: %s", client_id, key.c_str());
                locks.erase(key);
            } else {
                Debug("Lock held by someone else %lu: %s, %lu",
                        client_id, key.c_str(), locks[key]);
            }
        } else {
            Debug("Lock held by no one.");
        }
    }
}

void
LockServer::ExecConsensusUpcall(const string &str1, string &str2)
{
    Debug("ExecConsensus: %s\n", str1.c_str());

    Request request;
    Reply reply;

    request.ParseFromString(str1);
    string key = request.key();
    uint64_t client_id = request.clientid();
    reply.set_key(key);
    int status = 0;

    if (request.type()) { // Lock operation.
        if (locks.find(key) == locks.end()) {
            Debug("Assigning lock %lu: %s", client_id, key.c_str());
            locks[key] = client_id;
        } else if (locks[key] != client_id) {
            Debug("Lock already held %lu: %s", client_id, key.c_str());
            status = -1;
        }
    } else {
        Warning("Unlock operation being sent as Consensus");
        if (locks.find(key) == locks.end()) {
            Debug("Lock held by no-one %lu: %s", client_id, key.c_str());
            status = -2;
        } else if (locks[key] != client_id) {
            Debug("Lock held by someone else %lu: %s, %lu",
                    client_id, key.c_str(), locks[key]);
            status = -2;
        } else {
            Debug("Releasing lock %lu: %s", client_id, key.c_str());
            locks.erase(key);
        }
    }

    reply.set_status(status);
    reply.SerializeToString(&str2);
}

void
LockServer::UnloggedUpcall(const string &str1, string &str2)
{
    Debug("Unlogged: %s\n", str1.c_str());
}

} // namespace lockserver
