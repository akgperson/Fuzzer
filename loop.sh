#!/bin/bash

rm counter.txt
touch counter.txt
for i in $(seq 1 100); do
    tmpfile=/tmp/boolean$$.$i.smt2
    python3 ./boolean.py > $tmpfile 
    echo $tmpfile
    ./cvc4-2018-06-25-x86_64-linux-dbg --check-models --check-unsat-cores $tmpfile | tee -a counter.txt
done
all=$(grep -o 'sat' counter.txt | wc -l)
nUnsat=$(grep -o 'unsat' counter.txt | wc -l)
nSat=$((all - nUnsat))
echo number sat: $nSat
echo number unsat: $nUnsat
Ratio=$(((nSat*100) / (all)))
echo percent sat: $Ratio
echo $Ratio >> percents_boolean.txt
