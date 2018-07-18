#!/bin/bash

rm c.txt
touch c.txt
for i in $(seq 1 100); do
    tmpfile=/tmp/cexp$$.$i.smt2
    python3 ./CNFexp.py > $tmpfile 
    echo $tmpfile
    timeout 10s ./cvc4-07-17-2018 --check-models --check-unsat-cores $tmpfile | tee -a c.txt
done
a=$(grep -o 'sat' c.txt | wc -l)
nUnsat=$(grep -o 'unsat' c.txt | wc -l)
nSat=$((a - nUnsat))
echo number sat: $nSat
echo number unsat: $nUnsat
r=$(((nSat*100) / (a)))
echo percent sat: $r
echo $r >> percents_CNFexp.txt
