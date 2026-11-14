Bounded search evidence
=======================

This directory is supplementary. The primary result is deterministic and
reproducible without running any search.

Local transition reductions
---------------------------
local_merge.cpp computes an inductive finite-window overapproximation,
then tests direct state identification and a two-rewritten-row template.
It uses native coordinates (initial state 74, halt 254). For example, from
the extracted package root:

  g++ -O3 -std=c++17 search/local_merge.cpp -o local_merge
  ./local_merge machine/machine.native.tm 7 blank

Its final argument selects a blank start; omitting that argument includes
every initial tape window. The radius is the preceding integer argument.
The tested simulation must finish in at most 63 steps without leaving the
recorded window. A helper run may not revisit the merged keeper internally.
These restrictions are search-template bounds, not mathematical necessity.
local_search_receipts.json retains the observed runs, exact input hashes,
context counts, and positive-control rediscovery of the seven known folds.

Source variants
---------------
source_variants.py identifies complete axiom-head blocks in the inherited
191-token emitter and generates schema-preserving alternatives, including
parameter swaps and antecedent exchange. It uses the sibling machine/
directory and standard-library Python only. Running
python3 search/source_variants.py regenerates the three retained JSON files.
The mathematical reasons for preservation
are in Appendix C of the report. The negative-Gamma variants are separate
research leads and are not used in the main proof.

Fold-aware grammar searches
---------------------------
annealing/ contains the five corrected fixed-seed search runs, portable
C++17 sources, complete numeric inputs, logs, and the final radius-two
neighborhood check. Follow annealing/README.txt from that directory.
The wall-clock budgets make exact proposal counts host-dependent.
The recorded total is 39,661,078 proposals; no sub-195 hit was found.
The final neighborhood contained 49,513 distinct endpoint trees and also
had no sub-195 hit. Preliminary runs with incorrect collapsed-token
positions are excluded from these counts and from the package.

Optional secondary witnesses
----------------------------
annealing/secondary195/ and annealing/negative_gamma195/ contain separate
195-state candidates, their tables, and portable finite-check scripts.
Each script takes the primary inherited baseline directory as an argument;
from its own directory this is ../../../machine/baseline195.
Their READMEs state the exact command and the limits of the claims.
Their finite implementation checks passed. They are not substituted for
the main PA195DC mathematical endpoint or advertised as new kernel-checked
consistency-equivalence theorems.
