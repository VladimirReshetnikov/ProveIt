COMBINED OM EMITTER GRAMMAR SEARCH

This adapts the supplied ORH grammar search to the combined OM fixed rows.
The 135 fixed controls include 333, so its native 98/90 reader reuse is real.
The seed has 66 reader controls and seven folds, effective cost 59.
5,000,000 proposals, 1,546,687 accepted moves, best effective 59, no cost58 hit.
Seed 2026111428; max_iterations=5000000; observed 492.331 seconds.
The search samples reassociations; it is not an exhaustive lower bound.
Fitness is a nomination only; a prospective improvement needs full source,
physical, and blank initialization validation. No new 193-state result.

REPEAT (C++17):
  g++ -std=c++17 -O2 search.cpp -o search
  ./search OM_seeds.txt leaf_attrs.txt rerun 3600 2026111428 5000000
Use a sufficiently large time cap to finish the iteration budget. Wallclock
columns vary by host; pseudorandom order also depends on the C++ library.
Input templates and leaf attributes are bundled. No network required.

Attribution: adapted from docs/incoming/PA194ORH_research_2026-11-15.zip
at ProveIt commit 883da8d55452ea097910ed2509a1eefc833ce292. Applicable notices
are preserved in the top-level licenses directory.
