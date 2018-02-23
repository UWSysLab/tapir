// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * lockserver/client.cc:
 *   A single lockserver client with commandline interface.
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

#include "lockserver/client.h"

namespace {

void
usage()
{
    printf("Unknown command.. Try again!\n");
    printf("Usage: exit | q | lock <key> | unlock <key>\n");
}

} // namespace

int
main(int argc, char **argv)
{
    const char *configPath = NULL;

    // Parse arguments
    int opt;
    while ((opt = getopt(argc, argv, "c:")) != -1) {
        switch (opt) {
        case 'c':
            configPath = optarg;
            break;

        default:
            fprintf(stderr, "Unknown argument %s\n", argv[optind]);
        }
    }

    if (!configPath) {
        fprintf(stderr, "option -c is required\n");
        return EXIT_FAILURE;
    }

    lockserver::LockClient locker(configPath);

    char c, cmd[2048], *tok;
    int clen, status;
    string key, value;

    while (1) {
        printf(">> ");
        fflush(stdout);

        clen = 0;
        while ((c = getchar()) != '\n')
            cmd[clen++] = c;
        cmd[clen] = '\0';

        tok = strtok(cmd, " ,.-");
        if (tok == NULL) continue;

        if (strcasecmp(tok, "exit") == 0 || strcasecmp(tok, "q") == 0) {
            printf("Exiting..\n");
            break;
        } else if (strcasecmp(tok, "lock") == 0) {
            tok = strtok(NULL, " ,.-");
            if (tok == NULL) {
                usage();
                continue;
            }
            key = string(tok);
            status = locker.lock(key);

            if (status) {
                printf("Lock Successful\n");
            } else {
                printf("Failed to acquire lock..\n");
            }
        } else if (strcasecmp(tok, "unlock") == 0) {
            tok = strtok(NULL, " ,.-");
            if (tok == NULL) {
                usage();
                continue;
            }
            key = string(tok);
            locker.unlock(key);
            printf("Unlock Successful\n");
        } else {
            usage();
        }
        fflush(stdout);
    }

    return EXIT_SUCCESS;
}

namespace lockserver {

using namespace std;
using namespace proto;

LockClient::LockClient(const string &configPath) : transport(0.0, 0.0, 0)
{
    // Load configuration
    std::ifstream configStream(configPath);
    if (configStream.fail()) {
        Panic("Unable to read configuration file: %s\n", configPath.c_str());
    }
    transport::Configuration config(configStream);

    client_id = 0;
    while (client_id == 0) {
        random_device rd;
        mt19937_64 gen(rd());
        uniform_int_distribution<uint64_t> dis;
        client_id = dis(gen);
    }

    client = new replication::ir::IRClient(config, &transport, client_id);

    /* Run the transport in a new thread. */
    clientTransport = new thread(&LockClient::run_client, this);
}

LockClient::~LockClient() { }

void
LockClient::run_client()
{
    transport.Run();
}

bool
LockClient::lock(const string &key)
{
    Debug("Sending LOCK");

    string request_str;
    Request request;
    request.set_clientid(client_id);
    request.set_key(key);
    request.set_type(true);
    request.SerializeToString(&request_str);

    waiting = new Promise(1000);
    transport.Timer(0, [=]() {
            client->InvokeConsensus(request_str,
                bind(&LockClient::Decide,
                    this,
                    placeholders::_1),
                bind(&LockClient::LockCallback,
                    this,
                    placeholders::_1,
                    placeholders::_2));
            });

    int status = waiting->GetReply();
    delete waiting;

    if (status == 0) {
        return true;
    } else if (status == -1) {
        Debug("Lock held by someone else.");
    }
    return false;
}

void
LockClient::unlock(const string &key)
{
    Debug("Sending UNLOCK");

    string request_str;
    Request request;
    request.set_clientid(client_id);
    request.set_key(key);
    request.set_type(false);
    request.SerializeToString(&request_str);

    waiting = new Promise(1000);
    transport.Timer(0, [=]() {
            client->InvokeInconsistent(request_str,
                bind(&LockClient::UnlockCallback,
                    this,
                    placeholders::_1,
                    placeholders::_2));
            });

    waiting->GetReply();
    delete waiting;
}

string
LockClient::Decide(const set<string> &results)
{
    // If a majority say lock, we say lock.
    int success_count = 0;
    string key;
    for (string s : results) {
        Reply reply;
        reply.ParseFromString(s);
        key = reply.key();

        if (reply.status() == 0)
            success_count ++;
    }

    string final_reply_str;
    Reply final_reply;
    final_reply.set_key(key);
    if (success_count >= 2) {
        final_reply.set_status(0);
    } else {
        final_reply.set_status(-1);
    }
    final_reply.SerializeToString(&final_reply_str);
    return final_reply_str;
}

void
LockClient::LockCallback(const std::string &request_str, const std::string &reply_str)
{
    Debug("Lock Callback: %s %s", request_str.c_str(), reply_str.c_str());
    Reply reply;
    reply.ParseFromString(reply_str);

    Promise *w = waiting;
    waiting = NULL;
    w->Reply(reply.status());
}

void
LockClient::UnlockCallback(const std::string &request_str, const std::string &reply_str)
{
    Debug("Lock Callback: %s %s", request_str.c_str(), reply_str.c_str());

    Promise *w = waiting;
    waiting = NULL;
    w->Reply(0);
}

} // namespace lockserver
