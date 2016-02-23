#/bin/bash

procname=$1
check=1
while [ $check -gt 0 ]
do
    check=`pgrep -u $USER -x $procname | wc -l`
    sleep 1
done
