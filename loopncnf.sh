#!/bin/bash

rm cnt.txt
touch cnt.txt
for i in $(seq 1 100); do
    tmpfile=/tmp/b$$.$i.smt2
    python3 ./ncnf.py > $tmpfile 
    echo $tmpfile
    timeout 10s ./cvc4-07-17-2018 --check-models --check-unsat-cores $tmpfile | tee -a cnt.txt
done
xALL=$(grep -o 'sat' cnt.txt | wc -l)
xnUNSAT=$(grep -o 'unsat' cnt.txt | wc -l)
xnSAT=$((xALL-xnUNSAT))
echo number sat: $xnSAT
echo number unsat: $xnUNSAT
xratio=$(((xnSAT*100) / (xALL)))
echo percent sat: $xratio
echo $xratio >> percents_ncnf.txt
