AX grammar research: row symmetries, normalization, and implication bases
======================================================================

Outcome: no grammar below 128 rules and no new certified Turing machine.
The incumbent routing245 framework charges 117 states in addition to its
128 source grammar states. Every count here is a grammar count, not a newly
proved machine bound. The legacy framework_states=118 fields in inherited
search JSON are historical and are not used to count machines.

New search method
-----------------
The dictionary parser tracks the UNION of the existing grammar dependencies
of its chosen words. This avoids charging a shared helper on every use.
It keeps a finite beam of dependency masks at each source position. New
concatenation trees are subsequently materialized using exact set unions,
physical terminal orientation masks, and the six-zero/depth64 limits.
This permits shared joins to improve the parser's original upper bound.
Neither the finite beam nor the parenthesization heuristic is exhaustive
over grammars. Visiting all 8! row orders does not prove global optimality.

The original dictionary has 51 required core rules and 77 private AX rules.
The independently certified earlier DNE-mask32 dictionary has 53 core rules
and 75 private AX rules. These are different source/grammar configurations;
the second search composes the earlier normalization with row symmetries.

Completed runs
--------------
Original AX, all 40,320 row orders: beam4, 17.5834 seconds, best128.
Original AX, row/role mutation: beam8, 222,378 proposals, 180 seconds, best128.
Eleven new128 row-order seeds: 4,420,263 routing-annealer proposals total,
  30 seconds per seed, best128 for every seed.
DNE-mask32 AX, all 40,320 row orders: beam8, 32.2153 seconds, best128.
K/B/Peirce: beam8, 71,784 proposals, 120 seconds; best materialized134.
K/S/Peirce control: beam8, 47,282 proposals, 40.0002 seconds;
  parser bound134, best materialized133.

K= a -> (b -> a)
B= (a -> b) -> ((b -> c) -> (a -> c))
S= (a -> (b -> c)) -> ((a -> b) -> (a -> c))
P= ((a -> b) -> a) -> a

The K/B/P AX word has1321 fine atoms; K/S/P has1331. Despite the shorter
first word, the retained second grammar is one rule smaller. This comparison
is scoped to the supplied dictionary, input ordering/role search, and runs.
It does not show that every K/S/P implementation is smaller.

Finite independent audit
------------------------
Run from this directory:

  python3 verify_structural_candidates.py

The supplied record structural_audit.json passes39 retained grammars.
It checks all22 consumed route projections, all54 bootstrap locks, literal
word concatenation, real physical orientation masks, absence of unreachable
grammar rules, full source zero-run<=6 and source depth<=64. It also checks
the exact emitted AX word against the retained schema/order/role metadata.
The vendor_manifest.json file identifies410478 bytes of19 inherited inputs.

This is a finite source/grammar audit. It does not construct a transition
table, replay unbounded register instructions, prove a new blank start, or
mechanize a consistency equivalence. Source basis replacements additionally
need their complete high-level proof compiler and altered selector counts.

Reproduce optional searches
--------------------------
Python3 and a C++17 compiler suffice. All dependencies are vendored.

  python3 prepare_axiom_search.py
  g++ -O3 -std=c++17 search_axiom_dictionary.cpp -o search_axiom_dictionary
  ./search_axiom_dictionary axiom_search.txt enumerate-new.jsonl 90 29103 4 enumerate
  python3 materialize_axiom_search.py enumerate-new.jsonl

For normalized and basis inputs:

  python3 prepare_normalized_search.py
  ./search_axiom_dictionary normalized/input.txt normalized/enumerate-new.jsonl 90 57201 8 enumerate
  python3 materialize_axiom_search.py --metadata normalized/metadata.json normalized/enumerate-new.jsonl

  python3 prepare_basis_search.py kbp
  ./search_axiom_dictionary basis_kbp/input.txt basis_kbp/mutate-new.jsonl 120 440312 8 mutate
  python3 materialize_axiom_search.py --metadata basis_kbp/metadata.json basis_kbp/mutate-new.jsonl

Substitute ksp and40 seconds for the matched K/S/Peirce lane. Wall-clock
search counts vary across machines. Frozen candidates and finite audits
are the reproducible evidence, not identical time-limited trajectories.
The original222378-proposal run used the fixed-eight-row predecessor of
the generic-row C++ frontend; the retained source generalizes the same
algorithm to permit the ten-row basis controls.

refine_axiom_candidates.py 30 reruns the eleven original128 grammar seeds
with the attributed canonical/routing annealer. It makes one explicit
AX-word substitution in the source-shape constraints; no route equation
or bootstrap lock is omitted. It runs two independent jobs concurrently.

Logical scope and attribution
-----------------------------
An arbitrary order of the eight existing logical axiom schemes preserves
the high-level enumerator's theorem set after changing the selector for
rho_j to k_pi(j)=9-pos_pi(j). Independent bijections of (a,b,c) within each
row are handled by the inverse parameter permutation in its proof-compiler
leaf block. The fourth read parameter u is retained, and every row appears
once. This is a high-level witness translation, not a stepwise bisimulation
of every arbitrary candidate number and not a binary-machine proof.

The DNE-mask32 source equivalence, eight-row selector lemma, closed-atom
normalization, emitter, routing annealer, grammar/boot constraints, and
base implementation are inherited from the inspected ProveIt incoming
archives. Their NOTICE and license files are retained under vendor/.
Original logical machine attribution remains Mira-Cult, Jeff Ketchersid,
and Andrew James Wade as detailed by those files. New work here is the
dependency-union beam parser, shared materializer, composed search
campaigns, basis comparison, and independent finite audit.
