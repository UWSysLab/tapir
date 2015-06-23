# TAPIR

This repository includes code implementing several replicated and
transactional key-value stores.

The repo is structured as follows:

- /lib - the transport library for communication between nodes. This
  includes UDP based network communcation as well as the ability to
  simulate network conditions on a local machine, including packet
  delays and reorderings.

- /replication
  - /vr - implementation of viewstamped replication protocol
  - /ir - implementation of inconsistent replication protocol

-
