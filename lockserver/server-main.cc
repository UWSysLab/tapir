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
