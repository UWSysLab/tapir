#!/bin/bash

shard=$1    # which shard is this
config=$2   # path to config file
cmd=$3      # command to run
logdir=$4   # log directory

if [ "$#" -ne 4 ]; then
  echo "Usage: $0 shard configpath command logdir" >&2
  exit 1
fi

n=$(head -n1 $config | awk '{print $2}')
let n=2*$n+1

for ((i=0; i<$n; i++))
do
  let line=$i+2 
  server=$(cat $config | sed -n ${line}p | awk -F'[ :]' '{print $2}')
  command="ssh $server \"$cmd -c $config -i $i > $logdir/$shard.replica$i.log 2>&1 &\""
  #echo $command
  eval $command
done
