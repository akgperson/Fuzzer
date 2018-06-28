#!/bin/bash

tmpfile=/tmp/boolean$$.smt2
for i in $(seq 1 100); do
    python3 ./boolean.py > $tmpfile 
    ./cvc4-2018-06-25-x86_64-linux-dbg $tmpfile
done
