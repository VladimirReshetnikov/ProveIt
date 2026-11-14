Finite association searches
==========================

All C++ sources are standalone with the included headers. Example:

  g++ -O3 -std=c++17 exact_search_pruned.cpp -o exact_search
  ./exact_search 3000000 18519 replay18519

The third argument is an output prefix; the program writes PREFIX.ndjson.
Progress and the final result go to stderr. Use a new prefix to preserve
the historical receipts.

Completed runs (proposal slots, seed, source):

  exact18519    3000000 18519 exact_search_pruned.cpp
  exact18520    3000000 18520 exact_search_pruned.cpp
  hot18601     3000000 18601 exact_hot_pruned.cpp
  repair19901  3000000 19901 repair_exact.cpp
  repair19902  3000000 19902 repair_count.cpp
  scanner821001 3000000 21001 scanner8_search.cpp
  scanner821101 5000000 21101 scanner8_seed60.cpp

Total: 23,000,000 proposal slots. This is NOT a count of unique scored
grammars. Some proposals are rejected before scoring.

Scores are effective AX-reader cost before adding the 134-control core.
For the original scanner, score61 corresponds to195. For the eighth-zero
scanner add135, so score60 corresponds to195 and only score<60 improves it.
The two repair searchers also track encoding violations; score60 with a
positive violation count is a rejected194 candidate, not a valid machine.

The ordinary runs ended best61. Scanner821001 ended best61 (196 after
scanner cost); scanner821101 ended best60 (195). Both repair runs ended
at cost60 with remaining violations, one peak violation or four bad leaves.

The allocator checks simultaneous fold compatibility. Its local finite
test has an explicit bound in these heuristic programs; the independent
two-rotation exclusion uses exact cycle detection. No stochastic output
here is claimed to prove a lower bound or a complete physical runtime.
The complete source-contract/startup check remains necessary for acceptance.
