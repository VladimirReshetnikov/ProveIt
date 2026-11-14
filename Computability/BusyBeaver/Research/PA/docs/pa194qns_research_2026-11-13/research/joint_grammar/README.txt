Joint QNS fixed controller and exact Q-word reassociation
=======================================================

This is a bounded unsuccessful search, not a minimality result.

The controller has already applied the symmetric sum-guard fold.
templates.txt contains 134 remaining fixed controls and the Q AX tree.
leaf_attrs.txt records source address attributes required by the scanner.
Parameter-permutation mutations are disabled; reassociation preserves
the exact 190-token Q macro word.

Build and run from this directory:

    c++ -O3 -std=c++17 joint_anneal.cpp -o /tmp/qns-anneal
    /tmp/qns-anneal templates.txt leaf_attrs.txt /tmp/qns 240 202611132224

The output prefix above keeps replay results outside this release.
The actual observed run.log and qns.csv are retained.

Observed: 1,366,615 proposal slots; 220,787 accepted moves; 240.054 seconds;
best effective reader objective 60; zero penalty-free hits with objective
<=59. Such a hit would need simultaneous local fold and full physical
verification before claiming 193 states. Proposals may repeat grammars.

The C++ source adapts the supplied exact-word grammar search, retaining
the parent algorithm and history-fold scorer. The new frozen controller
and threshold target the concrete QNS composition. screen.cpp preserves
the additional scorer implementation used to prepare/review the run.
Time-limited proposal counts depend on processor speed; the accepted
194-state machine is reproduced deterministically by the top-level builder.
