#include <thread>

#include "lockserver/client.h"
#include "lib/udptransport.h"

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

    // Load configuration
    std::ifstream configStream(configPath);
    if (configStream.fail()) {
        Panic("Unable to read configuration file: %s\n", configPath);
    }
    transport::Configuration config(configStream);

    // Create lock client.
    UDPTransport transport(0.0, 0.0, 0);
    lockserver::LockClient locker(&transport, config);
    std::thread run_transport([&transport]() { transport.Run(); });

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

    transport.Stop();
    run_transport.join();
    return EXIT_SUCCESS;
}
