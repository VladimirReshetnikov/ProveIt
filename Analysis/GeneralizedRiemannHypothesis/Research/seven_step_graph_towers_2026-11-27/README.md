# Seven-step graph towers and the prime-step obstruction

Build the report with pdflatex seven_step_gap.tex (twice).

Replay the norm and moment certificate with python3 certificate.py. It
compares exact multiplication determinants with exact products of conjugates.

Compile the search with a C++17 compiler:
    c++ -O3 -std=c++17 exact_search.cpp -o exact_search

The default command ./exact_search checks M1=M2=0. The command
./exact_search lower checks all M1=0 lists at 17, 19, 23, and 31.
The expected output is included for both. A zero search score denotes an
empty subclass; a witness is printed only when a simple candidate exists.
Counts are counts of normal forms, not orbit counts. For these searches,
"simple" means nonzero, pairwise distinct signed residue classes.
