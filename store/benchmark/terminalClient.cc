// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * bench/terminal.cc:
 *   A terminal client for a distributed transactional store.
 *
 **********************************************************************/

#include "store/common/truetime.h"
#include "store/common/frontend/client.h"
#include "store/strongstore/client.h"
#include "store/weakstore/client.h"
#include "store/tapirstore/client.h"

using namespace std;

int
main(int argc, char **argv)
{
    const char *configPath = NULL;
    int nShards = 1;
    int closestReplica = -1; // Closest replica id.

    Client *client;
    enum {
        MODE_UNKNOWN,
        MODE_TAPIR,
        MODE_WEAK,
        MODE_STRONG
    } mode = MODE_UNKNOWN;

    // Mode for strongstore.
    strongstore::Mode strongmode;

    int opt;
    while ((opt = getopt(argc, argv, "c:N:m:r:")) != -1) {
        switch (opt) {
        case 'c': // Configuration path
        { 
            configPath = optarg;
            break;
        }

        case 'N': // Number of shards.
        { 
            char *strtolPtr;
            nShards = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0') ||
                (nShards <= 0)) {
                fprintf(stderr, "option -n requires a numeric arg\n");
            }
            break;
        }

        case 'm': // Mode to run in [occ/lock/...]
        {
            if (strcasecmp(optarg, "txn-l") == 0) {
                mode = MODE_TAPIR;
            } else if (strcasecmp(optarg, "txn-s") == 0) {
                mode = MODE_TAPIR;
            } else if (strcasecmp(optarg, "qw") == 0) {
                mode = MODE_WEAK;
            } else if (strcasecmp(optarg, "occ") == 0) {
                mode = MODE_STRONG;
                strongmode = strongstore::MODE_OCC;
            } else if (strcasecmp(optarg, "lock") == 0) {
                mode = MODE_STRONG;
                strongmode = strongstore::MODE_LOCK;
            } else if (strcasecmp(optarg, "span-occ") == 0) {
                mode = MODE_STRONG;
                strongmode = strongstore::MODE_SPAN_OCC;
            } else if (strcasecmp(optarg, "span-lock") == 0) {
                mode = MODE_STRONG;
                strongmode = strongstore::MODE_SPAN_LOCK;
            } else {
                fprintf(stderr, "unknown mode '%s'\n", optarg);
                exit(0);
            }
            break;
        }

        case 'r':
        {
            char *strtolPtr;
            closestReplica = strtod(optarg, &strtolPtr);
            if ((*optarg == '\0') || (*strtolPtr != '\0'))
            {
                fprintf(stderr,
                        "option -r requires a numeric arg\n");
            }
            break;
        }

        default:
            fprintf(stderr, "Unknown argument %s\n", argv[optind]);
            break;
        }
    }

    if (mode == MODE_TAPIR) {
        client = new tapirstore::Client(configPath, nShards,
                    closestReplica, TrueTime(0, 0));
    } else if (mode == MODE_WEAK) {
        client = new weakstore::Client(configPath, nShards,
                    closestReplica);
    } else if (mode == MODE_STRONG) {
        client = new strongstore::Client(strongmode, configPath,
                    nShards, closestReplica, TrueTime(0, 0));
    } else {
        fprintf(stderr, "option -m is required\n");
        exit(0);
    }

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

        if (clen == 0) continue;

        tok = strtok(cmd, " ,.-");

        if (strcasecmp(tok, "exit") == 0 || strcasecmp(tok, "q") == 0) {
            printf("Exiting..\n");
            break;
        } else if (strcasecmp(tok, "get") == 0) {
            tok = strtok(NULL, " ,.-");
            key = string(tok);

            status = client->Get(key, value);

            if (status == 0) {
                printf("%s -> %s\n", key.c_str(), value.c_str());
            } else {
                printf("Error in retrieving value\n");
            }
        } else if (strcasecmp(tok, "put") == 0) {
            tok = strtok(NULL, " ,.-");
            key = string(tok);
            tok = strtok(NULL, " ,.-");
            value = string(tok);
            client->Put(key, value);
        } else if (strcasecmp(tok, "begin") == 0) {
            client->Begin();
        } else if (strcasecmp(tok, "commit") == 0) {
            bool status = client->Commit();
            if (status) {
                printf("Commit succeeded..\n");
            } else {
                printf("Commit failed..\n");
            }
        } else {
            printf("Unknown command.. Try again!\n");
        }
        fflush(stdout);
    }

    exit(0);
    return 0;
}
