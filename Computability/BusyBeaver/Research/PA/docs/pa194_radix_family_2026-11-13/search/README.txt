BOUNDED REDUCTION SEARCHES
=========================

No verified table with fewer than 194 working states was obtained. The negative
results here apply only to the specified templates, screening conditions and
finite or time-bounded searches. They are not lower bounds on arbitrary TMs.

Main recorded runs
------------------
run194.log:       4,773,613 primary grammar proposals; best 134+60=194.
global194.log:    1,618,013 proposals allowing eligible fixed fold endpoints;
                 best 134+60=194.
split_macro/:      550,868 proposals exposing selected internal macro fragments;
                 best 134+60=194.
radix_candidates.json: finite decoder-DAG enumeration; 1,248 generated roots
                 with at most three auxiliary controls. The only non-four
                 coefficients reaching the 194 threshold were five and six.
runradix5.log:    1,196,159 proposals; best 135+59=194.
runradix6.log:    1,718,317 proposals; best 135+59=194.

Time-bounded replays can examine different numbers of candidates on another
machine. The numerical fitness is an optimistic/conservative template-specific
screen, not acceptance as a consistency machine. Surviving candidates still
require source binding, universal physical contracts and exact blank startup.

Python decoder enumeration, from the top level of the archive:

  python3 -B search/radix_search.py

This writes search/radix_candidates_replayed.json, preserving the recorded
radix_candidates.json. It imports the included construction/compiler.py.

C++ grammar searches (C++17), from this search/ directory:

  g++ -O3 -std=c++17 search_plateau.cpp -o search_plateau
  ./search_plateau primary194.txt leaf_attrs.txt replay_primary 300 73913

  g++ -O3 -std=c++17 search_global.cpp -o search_global
  ./search_global primary194.txt leaf_attrs.txt replay_global 300 2026111419

  g++ -O3 -std=c++17 search_radix.cpp -o search_radix
  ./search_radix radix5.txt attrs5.txt replay_radix5 180 2026111405
  ./search_radix radix6.txt attrs6.txt replay_radix6 180 2026111406

The seed printed in each original log is authoritative for its recorded run;
the commands above are reusable runs, not promises of identical timing.
The output prefix must name a writable location. These tools write candidate
grammars and a CSV trace. Raw fitness 59 for radix 5/6 means 135+59=194.

For the exposed-macro search, change into split_macro/:

  g++ -O3 -std=c++17 search_split.cpp -o search_split
  ./search_split primary194_split.txt leaf_attrs.txt replay_split 180 143701

The ready-to-run split source and input are frozen. prepare_split.py regenerates
them from the adjacent primary search and the included construction inputs.

Additional searches
-------------------
machine_searches/ includes a complete 576-table quotient closure of a specified
202-state parent, 459 neutral helper rewrites, a 1,275-table scanner-permutation
screen, source-invariant experiments, and the rejected 1,361-step bootstrap.
Its own README and receipts state exact scope. The adjacent pa194CSZ/ package
is the fully verified same-size auxiliary basis, not a result below 194.

These auxiliary inputs are kept distinct from the three main machines under
machines/. The final theorem and result table in the main report concern the
4R, 5 and 6 constructions.
