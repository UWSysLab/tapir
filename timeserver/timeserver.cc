// -*- mode: c++; c-file-style: "k&r"; c-basic-offset: 4 -*-
/***********************************************************************
 *
 * timeserver/timeserver.cc:
 *   Single TimeStamp Server.
 *
 **********************************************************************/

#include "timeserver/timeserver.h"

TimeStampServer::TimeStampServer()
{
    ts = 0;
}

TimeStampServer::~TimeStampServer() { }

string
TimeStampServer::newTimeStamp()
{
    ts++;
    return to_string(ts);
}

void
TimeStampServer::ReplicaUpcall(opnum_t opnum,
                               const string &str1,
                               string &str2)
{
    Debug("Received Upcall: %lu, %s", opnum, str1.c_str());

    // Get a new timestamp from the TimeStampServer
    str2 = newTimeStamp();
}

static void
Usage(const char *progName)
{
    fprintf(stderr, "usage: %s -c conf-file -i replica-index\n", progName);
    exit(1);
}

int
main(int argc, char **argv)
{
    int index = -1;
    const char *configPath = NULL;
    const char *transporttype = NULL;
    char *strtolPtr;
    // Parse arguments
    int opt;
    while ((opt = getopt(argc, argv, "c:i:t:")) != -1) {
        switch (opt) {
        case 'c':
            configPath = optarg;
            break;

        case 'i':
            index = strtoul(optarg, &strtolPtr, 10);
            if ((*optarg == '\0') || (*strtolPtr != '\0') || (index < 0)) {
                fprintf(stderr, "option -i requires a numeric arg\n");
                Usage(argv[0]);
            }
            break;
	case 't':
	    transporttype = optarg;
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
        fprintf(stderr, "unable to read configuration file: %s\n", configPath);
        Usage(argv[0]);
    }
    transport::Configuration config(configStream);

    if (index >= config.n) {
        fprintf(stderr, "replica index %d is out of bounds; "
                "only %d replicas defined\n", index, config.n);
        Usage(argv[0]);
    }

    Transport *t;
    if (strcasecmp(transporttype, "udp")) {
	t = new UDPTransport(0.0, 0.0, 0);
    } else if (strcasecmp(transporttype, "tcp")) {
	t = new TCPTransport(0.0, 0.0, 0);
    } else if (strcasecmp(transporttype, "rdma")) {
	t = new RDMATransport(0.0, 0.0, 0);
    } else {
	// default to zeus for now
	t = new ZeusTransport(0.0, 0.0, 0);
    }
    TimeStampServer server;
    replication::vr::VRReplica replica(config, index, t, 1, &server);

    t->Run();
    delete t;
    return 0;
}
