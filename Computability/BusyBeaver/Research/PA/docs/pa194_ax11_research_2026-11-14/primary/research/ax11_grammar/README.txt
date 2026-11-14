Bounded PA194AX11 decoder search
================================
The two frozen seeds use the new terminal push and no-push MP. One keeps
the original sixth logical head; the other uses the supplied Q exchange.
All search mutations in this run reassociate a fixed macro word.

Reproduce with a C++17 compiler, from this directory:
  c++ -O3 -std=c++17 search.cpp -o /tmp/ax11-search
  /tmp/ax11-search seeds.txt leaf_attrs.txt /tmp/ax11-output 240 202611140929

The stopping rule is elapsed wall time, so the exact proposal count is not
promised on another computer. This actual run tried 2,669,812 proposals,
accepted 138,489 moves, and obtained no effective reader score below 60.
With 134 fixed states this is 194 total. This is not a state lower bound.
The compiler and complete physical proofs, not this search, certify PA194AX11.

Source adapted from the pinned PA194 packet search/search_plateau.cpp and
screen.cpp, with parameter-permutation mutations disabled and target score
59. See the package license and provenance notices.
