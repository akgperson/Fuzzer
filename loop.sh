#!/bin/bash

for i in $(seq 1 100); do
    tmpfile=/tmp/boolean$$.$i.smt2
    python3 ./boolean.py > $tmpfile 
    echo $tmpfile
    ./cvc4-2018-06-25-x86_64-linux-dbg --check-models --check-unsat-cores $tmpfile 
done
