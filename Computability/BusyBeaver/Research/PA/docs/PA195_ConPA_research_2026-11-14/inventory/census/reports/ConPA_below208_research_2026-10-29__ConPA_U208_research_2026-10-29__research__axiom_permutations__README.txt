EXACT EXHAUSTION OF SEVEN INDEPENDENT SELECTOR PERMUTATIONS

Result
------
All 6^7 = 279,936 choices were evaluated. The minimum is 197 distinct
primitive source subtrees. Exactly four assignments attain that value:

    0000000   no selector renaming
    0001010   interchange b,c in rho4 and rho2
    0100000   interchange b,c in rho6
    0101010   both of the preceding changes

The coordinate order is G, rho6, rho5, rho4, rho3, rho2, rho1.
The six permutations are abc, acb, bac, bca, cab, cba. A digit states the
images of the old variables a,b,c in that order.

This result rules out an improvement in this precisely specified source
family. It is not a lower bound on Turing-machine states. The association
of the source tree, order of logical rows, all nonselector primitives,
interpreter, and tape representation are fixed. A source DAG of 197 nodes
does not itself constitute a 208-state machine, much less a 207-state
machine. Physical allocation, primitive runtime, startup and logical
calibration remain separate obligations for every changed source.

Reproduction
------------
Python 3.10+ and its standard library suffice. No network, external imports,
compiler, proof assistant, or third-party package is used.

    python3 exhaust.py
    python3 -O exhaust.py --output /tmp/axiom-permutation-check

The command works from any current directory. Without --output it rewrites
results/ relative to this script. It emits census.json, the complete cost
histogram, and the four minimizing source files. Every validation uses an
explicit require() function, so optimization mode cannot disable checks.

Inputs
------
inputs/sites.json is the exact Joint U209 source, containing 3,909 primitive
occurrences. Its native source tree has 197 distinct subtrees. The source
is common to the validated class-A U208 history reduction.

inputs/selectors.json contains the three exact, closed, 26-primitive
selector-load macros a, b, c. These were identified by exact matching to
retained K215 intervals [26,52), [52,78), [107,133), respectively; they are
not guessed from nearby native state names.

inputs/regions.json identifies seven complete unrestricted logical-schema
rows by half-open primitive ordinal intervals and supplies independently
audited selector occurrence counts. The executable locates the whole
selector subtrees directly and checks those counts and roles. The bounded
dominated row is excluded. inputs/manifest.json binds all three data files
by SHA-256 and records the upstream snapshot.

Mathematical scope
------------------
Each of the seven logical rows independently ranges over all triples of
natural-number formula selectors. A bijection of the parameter names in
one entire row therefore preserves its set of schema instances. Renaming
only selected subexpressions need not preserve that set and is outside
this search. Likewise, these permutations do not claim tuplewise equality
of the entire simultaneously emitted axiom bundle; the preserved object
is the independently enumerated set of instances of each complete row.

Exact scoring identity
----------------------
The source tree is partitioned into fixed subtrees, whole selector choices,
and binary pair templates above those choices. Identical templates are
shared. Every possible interior node of every selector macro already
occurs in the unchanged source; the script checks this set inclusion.
Consequently there are exactly 146 constant nodes.

Primitive subtree length is unchanged by any selector substitution. Of
the varying pair templates, 39 have a length that belongs to no fixed node
and no other varying template. They contribute exactly 39 distinct nodes
for every assignment. All remaining possible coincidences occur among
49 templates. Each such template depends on only one logical row. For
each template the script enumerates all of its possible selector choices,
constructs its exact hash-consed tree, and records the resulting node ID.
There are 208 IDs in the union of the fixed nodes and these finite lookup
tables. A bitset union counts all coincidences exactly for each of the
279,936 assignments. The final score is 39 plus that union's cardinality.

As an implementation cross-check, 343 fixed reproducible assignments are
also constructed directly from the full original source tree. Every
minimizer is independently reconstructed and its complete distinct-node
set is counted before its source is written. The finite count, histogram
sum and minimum multiplicity are explicitly checked. These cross-checks
supplement the exact decomposition; they are not the basis for claiming
that the parameter space was exhausted.

Files
-----
exhaust.py              self-contained executable
inputs/                 exact source, selector macros, row intervals, hashes
results/census.json     complete histogram, minima, hashes, decomposition
results/*.sites.json    all four minimizing complete source streams
replay.log              retained ordinary replay output
verification.json      ordinary versus python -O replay comparison

This directory contains a bounded negative research result, not a new
smaller machine or a proof-assistant certificate of the inherited theory.
