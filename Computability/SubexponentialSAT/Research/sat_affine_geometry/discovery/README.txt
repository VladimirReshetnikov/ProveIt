OPTIONAL DISCOVERY LOGS; NOT PART OF THE CORRECTNESS GATE

search.cpp is the finite heuristic search used to find four contraction
plans with a small support-sum certificate. It fixes the first plan and
swaps entries in the remaining three permutations, evaluating the exact
integer Q after each proposal. A deterministic random seed is used, but
C++ library shuffle/distribution implementations can differ. The search
is not an optimization proof, and its floating-point acceptance rule is
not used by the mathematical certificate.

Recorded best-so-far logs for r=12 and r=13 are included. The frozen
twelve-group plan selected in data/portfolios.json is independently
verified by code/check_portfolios.py; the thirteen-group search did not
set the final headline. The affine nine-group menu is a direct finite
geometry construction, independently certified as Q=5400.

For an optional replay on a GNU C++17 environment:
  g++ -O3 -std=c++17 search.cpp -o search
  ./search 12 20000

This exploratory program was written for r=12,13. Its fixed Gram arrays
hold at most 64 operation supports; do not use it for r>23. It is not
hardened as a general CLI. Replaying it is unnecessary for verification;
the Python certificates are the supported correctness interface.
