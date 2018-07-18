#!/bin/bash

rm counter.txt
touch counter.txt
for i in $(seq 1 100); do
    tmpfile=/tmp/boolean$$.$i.smt2
    python3 ./boolean.py > $tmpfile 
    echo $tmpfile
    timeout 10s ./cvc4-07-17-2018 --check-models --check-unsat-cores $tmpfile | tee -a counter.txt
done
all=$(grep -o 'sat' counter.txt | wc -l)
nUnsat=$(grep -o 'unsat' counter.txt | wc -l)
nSat=$((all - nUnsat))
echo number sat: $nSat
echo number unsat: $nUnsat
Ratio=$(((nSat*100) / (all)))
echo percent sat: $Ratio
echo $Ratio >> percents_boolean.txt
