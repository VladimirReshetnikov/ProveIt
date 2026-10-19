Fine-atom grammar research for routed245
=======================================

Result status
-------------
No machine with fewer than 245 states was constructed in this lane. The
complete frozen 245-state machine remains the baseline. The new material is
an exact normalization of its 44 closed atoms to 30 finer atoms, a generalized
grammar search retaining all 44 existing physical implementations, independent
source checks, and a restricted finite-substrate solver result.

Baseline
--------
ProveIt commit 6446ff5668307a2ac6aee1896037f0b792090389.
Use the recovered zfc245-proof-20261018 package described by ProveIt's
SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/
intake-164-reproduction.md. The package must contain inputs/, grammar.json,
and code/state_reduction/anneal_routes_zero6.cpp. No baseline files are edited.

For the search scripts, point ZFC245_PACKAGE to that package's absolute path.
For verify_fine_identities.py, pass the package explicitly with --package.
The grammar_model.py default finds ../packages/zfc245-proof-20261018 when
the delivery is unpacked with that original workspace arrangement.

Independent verification, Python standard library only
-----------------------------------------------------
python3 -B verify_fine_identities.py --package /path/to/zfc245-proof-20261018 \
  --candidate fine-seed9022.json --identities fine-atom-identities.json \
  --output fresh-fine-check.json

This recomputes rather than trusts the 44 normal forms; checks all 22 routed
projections, all 54 bootstrap equations, every rule's exact word and terminal
orientation, complete reachability, the exact ordered 6,460 source instruction
leaves, maximum source zero run and source depth. It certifies the forced
source path 1111000000 under the frozen bootstrap equations. It does not check
the complete binary runtime for a new machine.

Generalized fine-atom annealing
------------------------------
env ZFC245_PACKAGE=/path/to/zfc245-proof-20261018 python3 -B prepare_fine_search.py
g++ -O3 -std=c++17 anneal_fine.cpp -o search_fine
./search_fine fine-grammar.txt fine-constraints.txt fresh-fine.json 600 9022 127 \
  fine-boot54.txt fine-current128.resume

The retained discovery run used 6,939,406 proposals in 600.002 seconds and
found no improvement below 128 grammar rules. Timed runs can execute different
numbers of proposals on other systems. All 44 normalized terminal words retain
their original physical entry-orientation masks. The 14 compound terminals
add no states to the existing framework; their states are already counted.

Literal-word control search
---------------------------
The unmodified original anneal_routes_zero6.cpp was compiled with g++ -O3.
It was run with the original route-grammar.txt, route-constraints.txt,
bootstrap-lock54.txt, current128.resume, seed 8841, 600 seconds and target127.
The result is resume128-seed8841.json and its complete text log. It proposed
14,211,995 moves, retained 128 rules, and does not establish minimality.

Coordinated private-subtree reparsing
-----------------------------------
env ZFC245_PACKAGE=/path/to/zfc245-proof-20261018 python3 -B cut_reparse.py \
  --rounds 20 --seed 10 --output fresh-cut.json

This replaces private descendant subgraphs in a single proposal, using the
remaining live words and the 44 opaque terminals as its parsing dictionary.
The retained run generated 563 concrete proposals over 20 rounds and found no
improvement below 128 rules. Its early dictionary filter intentionally makes
the searched neighborhood finite and incomplete.

Finite-substrate mixed integer models
------------------------------------
Requires numpy and scipy.optimize.milp (retained run: SciPy 1.17.0; bundled
HiGHS version appears in each log). These are optional search dependencies.
The independent normalization checker has no such dependency.

env ZFC245_PACKAGE=/path/to/zfc245-proof-20261018 python3 -B milp_reparse.py \
  --rounds 2 --seconds 120 --new-limit 2 --bound 127 \
  --output fresh-two-new-result.json

The two-round closure has 917 potential nonterminal words and 3,384 potential
productions. It fixes 43 complete productions: the 27 bootstrap productions
plus the additional productions traversed by the existing entry routes. All
mandatory roots and current route words are active. Atom orientations are
enforced. No source zero-run/depth bound is imposed, so those constraints are
relaxed rather than being responsible for infeasibility.

HiGHS reported INFEASIBLE in 8.187 seconds for <=127 active grammar nodes with
at most two nonincumbent word nodes. This is a solver-reported bounded result
for this explicit universe and these frozen routes, not a universal lower
bound, a checked proof-assistant theorem, or an obstruction to changing more
than two helper words. A fresh run with the explicit incumbent positive
control also reports INFEASIBLE in 10.064 seconds; use
milp-two-new-checked-result.json and milp-two-new-checked.log for that run.
The positive control verifies every generated model constraint against the
128-rule incumbent, whose sole violation is the requested 127-rule bound.
The unrestricted model timed out after 181.384 seconds without an incumbent;
the three-new-helper relaxation timed out after 90.037 seconds without an
incumbent. Neither timeout supports a nonexistence claim.

Files and provenance
--------------------
grammar_report.tex is a report section for incorporation into a larger paper.
fine-atom-identities.json records all 44 normal forms and underlying AST IDs.
fine-search-check.json is the independent retained result for the final
normalized search output. fine-identities-check.json is the original-incumbent
normalization check. The .cpp search is adapted from the routed245 code, itself
attributed there to earlier ProveIt annealing. Preserve the upstream NOTICE
and licenses when incorporating inherited code. Newly written checker and
search orchestration impose no additional licensing restriction.

Do not interpret the abstract JSON field framework_states=118 as the final
literal framework count. That field is inherited from the original search
format, before removing one scanner state. Routed245's actual framework has
117 states. A 128-rule grammar therefore does not improve the 245-state total.

Independent review of the finite-theory reduction
------------------------------------------------
fc_assignment_review.json records the earlier ordinary mathematical review
of the assignment-only quotient/reconstruction theorem. Its exact replay is
preserved in skolem-review-replay/. fc_guard_reflexivity_review.json extends
that review to reconstruction of G and derivation of Eq reflexivity. The
fresh final replay in skolem-corollary-review-replay/ is byte-identical to
all 21 author outputs from theory_work/skolem_reduct.py. Final metrics are
20 clauses / 53 literals / 1,134 template bits for the FC15 variant and
21 / 57 / 1,341 for FC16. These are theory-template counts, not machine
state counts. The review checks exact AST substitutions for the two-premise
reflexivity derivation and all six variable-only native G occurrences.

The finite label checker structurally imposes the globally derived Eq
reflexivity. Its bounded stages must therefore be described as admissibly
strengthened rather than necessarily exact truncations of the final CNF.
The raw_guard option avoids silently reimposing G transport.

fc15_without_e_countermodel.tex is a self-contained further boundary result.
It constructs a model on N x {0,1} of the fifteen FC15 native templates
with Eq as a predicate, plus all original completion except E transport.
Even all nine function-congruence rows hold. Eq is not genuine equality;
this is not a model of the genuine-equality native FC15 theory. A ground
E-transport instance fails, as does the FC16 added extensionality row.
Thus simply dropping E transport from the final FC15 target destroys the
desired consistency calibration. The mathematical model is infinite.

To reproduce its finite input diagnostics against the immutable ASTs:

python3 -B fc15_without_e_countermodel.py \
  --reference /path/to/theory_work/reference \
  --output fresh-fc15-without-e.json

The retained run evaluates 203,478 assignments from {0,1,2} x {0,1} over
28 exact native/completion rows, with unbounded intermediate arithmetic.
It separately checks the ground E-transport and FC16 failures. These
finite samples diagnose the displayed universal proof; they are not a
finite carrier model or a substitute for the infinite-model argument.
