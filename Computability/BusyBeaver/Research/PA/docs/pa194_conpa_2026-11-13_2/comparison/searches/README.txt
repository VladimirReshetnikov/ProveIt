Bounded, reproducible exploratory association searches
=====================================================

Each .cpp file is a standalone C++17 search driver. Its .txt input contains
the full fixed transition rows, macro terminal attributes, initial tree,
and allowed token words. No source repository or Python import is needed
to rerun these C++ searches. For example:

  c++ -O3 -std=c++17 separate_search.cpp -o separate_search
  ./separate_search separate_input.txt 1000 9491013

Exact invocation arguments, completed limits, seeds and logs are in
bounded_search_ledger.json. Search outputs are written to the current
directory, so use an isolated directory to preserve the delivered records.
The default C++ runtime and standard-library implementation can affect the
trajectory; the delivered machine certificates do not rely on search replay.

The score counts new readers minus a compatibility-sensitive fold objective.
An inexpensive matching bound is used before exact simultaneous-fold checks.
An estimated 197-state h1/h2/h6 result has not been built and certified as a
complete machine. The separate195 intermediate was fully built and checked.
The eventual PA194 success came from the separate190 continuation performed
by the emitter search; its selected grammar and complete proof artifacts are
in the primary pa194 directory, with the main search provenance supplied
elsewhere in the packet.

The h1/h2/h6 relocation arguments in mathematics are exploratory ordinary
proof notes and are not dependencies of PA194. All these words retained the
same total 191-token length. The successful machine retains the original
190-token separate head word without any relocation of that kind.

These are finite heuristic searches, not exhaustive enumeration and not
lower-bound proofs. Mutation slots count visits, including skipped or repeated
shapes; they must not be described as distinct verified machines.
