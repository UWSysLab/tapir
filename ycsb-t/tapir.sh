#! /usr/bin/env bash

java -cp tapir-interface/target/tapir-interface-0.1.4.jar:core/target/core-0.1.4.jar:tapir/target/tapir-binding-0.1.4.jar:javacpp/target/javacpp.jar -Djava.library.path=libs/ com.yahoo.ycsb.Client -P workloads/workloada -load -db com.yahoo.ycsb.db.TapirClient -p tapir.configpath=../store/tapirstore/local -p tapir.nshards=1 -p tapir.closestreplica=0
