#!/bin/bash

if [ "$#" -ne 4 ]; then
  echo "Usage: $0 command begin_id ncopies" >&2
  exit 1
fi

cmd=$1
begin=$2
copies=$3
logdir=$4

let end=$begin+$copies

for ((i=$begin; i<$end; i++))
do
	#    command="DEBUG=all $cmd > $logdir/client.$i.log 2>&1 &"
    command="sudo -S nice -n -19 chrt -f 50 taskset 0x20 $cmd > $logdir/client.$i.log 2>&1 &"
#   echo $command
    eval $command
    #sleep 100
done
