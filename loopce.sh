#!/bin/bash

rm c.txt
touch c.txt
for i in $(seq 1 100); do
    tmpfile=/tmp/cexp$$.$i.smt2
    python3 ./CNFexp.py > $tmpfile 
    echo $tmpfile
    ./cvc4-07-17-2018 --check-models --check-unsat-cores $tmpfile | tee -a c.txt
done
all=$(grep -o 'sat' c.txt | wc -l)
nUnsat=$(grep -o 'unsat' c.txt | wc -l)
nSat=$((all - nUnsat))
echo number sat: $nSat
echo number unsat: $nUnsat
Ratio=$(((nSat*100) / (all)))
echo percent sat: $Ratio
echo $Ratio >> percents_CNFexp.txt
