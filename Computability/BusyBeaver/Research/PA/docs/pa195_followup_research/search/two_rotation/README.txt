Exhaustive one- and two-rotation neighborhood of PA195
===================================================

Scope
-----
The seed is exactly the 191-token AX macro grammar in the supplied PA195
package. Macro leaves remain fixed. A move is either:

1. A binary association rotation applied simultaneously to every occurrence
   of one distinct ordered subtree; or
2. A binary association rotation at one specified occurrence.

Both directions ((a,b),c) <-> (a,(b,c)) are allowed wherever defined.
All first moves and all second moves from every distinct first result are
enumerated. An intermediate grammar is retained even if it violates an
encoding gate. The final grammar is admitted exactly when max_zero<=6,
max_zero_ending_in_INC<=5, expanded AX depth<=39, node72 is never a right
child, and node142 is never a left child.

Canonicalization traverses the ordered tree left before right, assigning
an index on first completion of each distinct subtree. Duplicate keys are
compared as complete binary strings. No equality decision relies on a
truncated or collision-prone digest. The .keys.bin file gives every key in
census-id order, as a 4-byte little-endian length followed by the serialized
key. A key consists of signed 32-bit little-endian integers: root index,
number of rules, then the two children of every rule in order. Negative
children are fixed macro leaf identifiers, matching current_inputs.hpp.

Scoring
-------
For every admitted grammar, allocation preserves 134 inherited controls,
recognizes the existing two- and four-increment macros, and generates the
same contextual fold options as the reference reader allocator. Compatible
sets are searched exhaustively, including all available helper choices.
The bipartite matching is only an upper bound; it is not accepted as proof
that folds can coexist. Every selected set is checked in the final folded
table. Local compatibility uses exact cycle detection on the finite
state/head/two-cell-tape configuration space, not a finite fuel cutoff.
The state score is 134+allocated_readers-compatible_folds.

Results
-------
The summary JSON gives exact counts and histograms. The census TSV records
all unique grammar keys' one-step and two-step reachability flags, encoding
gate outcomes, and exact compatible-fold scores. Nonadmitted entries use
-1 for the state score. The seed is included in the union census.

The independent Python program enumerates the neighborhood again as nested
immutable tuples, compares the complete key sets and operation-reachability
flags, recalculates macro attributes from the pinned Lean source, rebuilds
the physical tables, and recomputes every admitted compatible-fold score.
Its receipt and log record the completed comparison.

This is a bounded exclusion for the specified neighborhood and contextual
fold allocator. It is not a lower bound for all PA machines, all grammars,
or all possible folding and compilation methods. No improving state score
was found, so no candidate from this search required full symbolic runtime
validation. A score 195 tie is not presented as a newly verified consistency
machine merely because it passes the encoding gates.

Reproduction
------------
From this directory, using a C++17 compiler and Python 3:

  g++ -O3 -std=c++17 two_rotation_search.cpp -o two_rotation_search
  ./two_rotation_search pa195_neighborhood
  python3 verify_neighborhood.py /path/to/extracted/pa195_conpa/pa195

The Python verifier uses only the standard library and reads the supplied
PA195 grammar plus its pinned reference inputs. It imports neither the C++
search code nor the vendored Python compiler. Keep the PA195 reference
folder unchanged. The full source instruction runtime and arithmetic
calibration are separate from the bounded search result.
