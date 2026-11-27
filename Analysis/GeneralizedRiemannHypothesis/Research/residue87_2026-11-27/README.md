# Six-term exclusions at discriminant -87

This report improves the residue-pattern coverage in ProveIt's merged GRH
article. It does not settle the remaining cases or assume RH or GRH.

Build the manuscript: pdflatex residue87.tex (twice).
Replay the exact counts with:
    c++ -O3 -std=c++17 certify.cpp -o certify
    python3 input.py | ./certify

The expected output is in verification.txt. input.txt also records the
two modular input vectors. No external libraries are required.
