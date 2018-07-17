#!/bin/bash

rm count.txt
touch count.txt
for i in $(seq 1 100); do
    tmpfile=/tmp/booln$$.$i.smt2
    python3 ./cnf.py > $tmpfile 
    echo $tmpfile
    ./cvc4-2018-06-25-x86_64-linux-dbg --check-models --check-unsat-cores $tmpfile | tee -a count.txt
done
ALL=$(grep -o 'sat' count.txt | wc -l)
nUNSAT=$(grep -o 'unsat' count.txt | wc -l)
nSAT=$((ALL-nUNSAT))
echo number sat: $nSAT
echo number unsat: $nUNSAT
ratio=$(((nSAT*100) / (ALL)))
echo percent sat: $ratio
echo $ratio >> percents_cnf.txt
