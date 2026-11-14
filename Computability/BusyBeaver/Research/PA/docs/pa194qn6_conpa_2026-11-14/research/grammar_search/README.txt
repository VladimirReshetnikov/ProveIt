Bounded grammar and decoder investigations, 14 November 2026
===========================================================

This folder records unsuccessful searches for a reduction below 194. It
must not be described as a lower-bound proof. SUMMARY.json is generated
from the actual execution logs by python3 summarize.py; incomplete runs
are explicitly marked incomplete. The full source/calibration validation
would be needed before accepting any search hit as a consistency machine.

Source snapshot: VladimirReshetnikov/ProveIt,
2337ce611a26e308697ccbddb2a1636f989f01c3.

New search moves
----------------

The inherited plateau search replaces every occurrence of a shared subtree
when rotating it. search_occurrence.cpp adds rotations of one occurrence,
allowing a shared subtree to be split and then refactored in its different
contexts. search_reparse.cpp additionally performs dynamic programming over
the whole emitted macro word, using current shared subtrees as a dictionary
and randomly omitting some dictionary entries. Every such structural move
preserves the expanded macro word. The inherited independent parameter-role
permutations remain available for the six unconditional logical heads.

screen_global.cpp extends the compatible two-cell history-fold candidates
to all non-arithmetic fixed controls as well as AX readers. It accounts for
all incoming transitions. A candidate requires that every incoming move is
to the right and writes the same history bit. Start 74 and the arithmetic
oracle controls are excluded. The final simultaneous fold check executes
every history/read-bit case, requiring the exact old endpoint control,
head displacement and two-cell tape after at most 20 transitions. This is
a sufficient local certificate, not a characterization of all valid folds.

screen_fixedreuse.cpp also interns a newly generated pure decoder pair
against exact fixed rows (0 R left, 1 R right). In particular, QN6's fixed
state 330 implements three literal increments and can be reused in AX.
The obsolete special treatment of four increments as state 190 is removed:
in QN6, state 190 implements SIX increments. The expanded AX word has three
maximal runs of three literal increments, starting at positions 61, 73, 89.
All 64 direct contraction/anchor choices were scored. The unchanged parse
scores 194; every parse with a forced triple contraction scores at least 197.
A separate annealing run forces use of the triple macro to explore beyond
this initial cost barrier. These are search scores, not accepted new tables.

Alternate coefficient layouts
-----------------------------

The final fixed-row-reuse screens also compare coefficient-six trees 3+3
(with either triple orientation), 2+4, 4+2, and coefficient-five trees 3+2
and 2+3 (with either triple orientation). The original right-associated
triple keeps the 41/99 fold; the other direct layouts lose it and initially
score 195. Separate 150-second annealing runs examine the best coefficient-
five layout and two alternative coefficient-six layouts.

Additional semantic words
-------------------------

E3 and E4 exchange the two curried antecedents in, respectively, the first
and second equality/membership congruence heads. Q exchanges the antecedents
of the quantified distribution head. These are fixed propositional proof
transformations. E3Q composes E3 with Q. GammaH changes the separately emitted
diagonal instance from Gamma(A) to Gamma(H). The transformed words remain
190 macro tokens. Equality-head words were supplied by the theory analysis.
A theory-level preservation argument alone does not validate a physical table.

QNS6 interference
-----------------

The QNS symmetric-Shift fold and the radix-six fold both normally eliminate
control 41. They cannot simply be counted twice. Four one-helper increment-six
trees (3+3 in either orientation, 2+4, 4+2) score 195 after compatible folds.
The action_merge.cpp screens then try arbitrary one-step replacement actions
followed by local detours of at most 80 steps, first in 9-cell and then 17-cell
abstract windows. All eight screens return zero candidates. The window
abstraction starts with all windows at control 74 and nondeterministically
introduces either bit at a boundary. This is a sound overapproximation for
the particular local-rewrite search; it does not rule out a different global
simulation or a different initialization scheme.

Reproduction
------------

C++17 and Python 3 standard libraries suffice. From this folder, examples:

  g++ -O3 -std=c++17 search_occurrence.cpp -o search_occurrence
  ./search_occurrence inputs/start194.txt inputs/leaf_attrs.txt rerun_occurrence 240 202611140815

  g++ -O3 -std=c++17 search_fixedreuse.cpp -o search_fixedreuse
  ./search_fixedreuse inputs/QN6.txt inputs/leaf_attrs.txt rerun_qn6 300 202611142356

  g++ -O3 -std=c++17 search_forced_inc3.cpp -o search_forced_inc3
  ./search_forced_inc3 inputs/QN6_forced_inc3.txt inputs/leaf_attrs.txt rerun_forced 240 202611150004

  g++ -O3 -std=c++17 action_merge.cpp -o action_merge
  ./action_merge inputs/qns6_3a3a.native.tm 8 80

  python3 summarize.py

Searches stop after a wall-clock budget. Proposal counts and final pools may
therefore differ on another computer even with the recorded random seeds.
Saved logs give the actual runs used for this report.

Attribution
-----------

screen.cpp, search_plateau.cpp and action_merge.cpp are copied from
PA/docs/pa194_conpa_2026-11-13/search at the pinned source. The variants are
adaptations of those files. inputs/leaf_attrs.txt and the primary fixed
control/tree input originate in that packet. Its attribution credits the
PA195 research search and James Chang's PA196 work. The other fixed tables
and Q grammar are derived from the delivered QNS and QN6 packets. Original
license files are retained in licenses/. New files in this folder are
research adaptations, not proof-assistant checked endpoints.
