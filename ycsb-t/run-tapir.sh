#! /usr/bin/env bash

# Copy the shared library to libs folder.
mkdir -p libs
cp ../libtapir/libtapir.so ./libs/

# Make the tapir binding using maven
mvn clean package

# Load the records in Tapir
java -cp tapir-interface/target/tapir-interface-0.1.4.jar:core/target/core-0.1.4.jar:tapir/target/tapir-binding-0.1.4.jar:javacpp/target/javacpp.jar \
-Djava.library.path=libs/ com.yahoo.ycsb.Client -P workloads/workloada \
-load -db com.yahoo.ycsb.db.TapirClient \
-p tapir.configpath=../store/tools/shard -p tapir.nshards=1 -p tapir.closestreplica=0 > load.log 2>&1

# Run the YCSB workload
java -cp tapir-interface/target/tapir-interface-0.1.4.jar:core/target/core-0.1.4.jar:tapir/target/tapir-binding-0.1.4.jar:javacpp/target/javacpp.jar \
-Djava.library.path=libs/ com.yahoo.ycsb.Client -P workloads/workloada \
-t -db com.yahoo.ycsb.db.TapirClient \
-p tapir.configpath=../store/tools/shard -p tapir.nshards=1 -p tapir.closestreplica=0 > run.log 2>&1
