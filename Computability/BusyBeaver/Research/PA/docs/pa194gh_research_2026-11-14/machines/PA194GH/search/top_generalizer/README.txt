Visible-top generalizer experiment — NOT a claimed consistency machine
=====================================================================

Delete the initial copyH token, so AX stores U(c,t) and no raw old top.
The emitter becomes 189 tokens and pushes 9 entries. The cache-only Shift
version is rejected by the exact even-residue invariant in obstruction.tex
and check_invariant.py; it cannot reach its halting test from zero.

The original sum-Shift version avoids that simple obstruction, but a
correct all-store proof compiler has not been found. Its generalized Push
stores U(0,t) rather than t. The old proof compiler cannot be reused.
No literal table here is presented as a PA-consistency machine.

A new stochastic search used sum-Shift fixed rows, 3,000,000 main iteration
slots and seed 202611140389. See top_sum_search.json for exact evaluation
counts. The best optimistic effective reader score remained 60, for a
projected 134 + 60 = 194 states. This is not a lower bound. Compatible folds,
physical checks and a command compiler would still be needed for any
better search score.

Reproduce symbolic emitter/invariant:
    python3 -B check_invariant.py

Reproduce search:
    g++ -O3 -std=c++17 source_search.cpp -o search_top
    ./search_top 3000000 202611140389 replay

The candidate numerical stack semantics and precise rejection proof are
included because they resolve a tempting state-reduction direction.
