// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
// vim: set ts=4 sw=4:
/***********************************************************************
 *
 * qwstore/replica.cc
 *   Single QWStore storage server executable
 *
 **********************************************************************/

#include "qwstore/replica.h"

using namespace std;
using namespace qwstore;

static void Usage(const char *progName)
{
    fprintf(stderr, "usage: %s -c conf-file -i replica-index\n",
            progName);
    exit(1);
}

int
main(int argc, char **argv)
{
    int index = -1;
    const char *configPath = NULL;
    const char *keyPath = NULL;

    // Parse arguments
    int opt;
    while ((opt = getopt(argc, argv, "c:i:f:")) != -1) {
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
                    fprintf(stderr,
                            "option -i requires a numeric arg\n");
                    Usage(argv[0]);
                }
                break;
            }
            case 'f':   // Load keys from file
                keyPath = optarg;
                break;

            default:
                fprintf(stderr, "Unknown argument %s\n", argv[optind]);
                break;
        }
    }

    if (!configPath) {
        fprintf(stderr, "option -c is required\n");
        Usage(argv[0]);
    }

    if (index == -1) {
        fprintf(stderr, "option -i is required\n");
        Usage(argv[0]);
    }

    // Load configuration
    std::ifstream configStream(configPath);
    if (configStream.fail()) {
        fprintf(stderr, "unable to read configuration file: %s\n",
                configPath);
        Usage(argv[0]);
    }
    specpaxos::Configuration config(configStream);

    if (index >= config.n) {
        fprintf(stderr, "replica index %d is out of bounds; "
                "only %d replicas defined\n", index, config.n);
        Usage(argv[0]);
    }

    UDPTransport transport(0.0, 0.0, 0);
    Server *server;

    server = new Server(config, index, &transport, new QWStore());

    if (keyPath) {
        string key;
        ifstream in;
        in.open(keyPath);
        if (!in) {
            fprintf(stderr, "Could not read keys from: %s\n", keyPath);
            exit(0);
        }
        for (int i = 0; i < 100000; i++) {
            getline(in, key);
            server->Load(key, key);
        }
        in.close();
    }

    transport.Run();

    return 0;
}
