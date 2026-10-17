CONCRETE MACHINE RESULTS
========================

Result 1: a new composition control, still 253 working states
-----------------------------------------------------------

composed253.tm combines two previously attributed transformations:

* Source27's four-row decoder reassociation of public253. The frozen faster253
  input has SHA256 d5b7a357dbf4dd9d18c8e1aa04dc0c3c0e1b8f349853b7558d1a096a15684412.
  Its bootstrap is 312935 steps, saving 40 from public253.
* The incoming report zfc_consistency_research_20261016's guarded shortcut
  compact60/read0: 0 L45 -> 0 R51. On the public table, that saves 80 boot steps.

This run does not assume that a guard proved on the original table survives
the first modification. It computes a fresh radius-two invariant on faster253
and independently checks all of its 7044 closure obligations. The 3530 admitted
state/window pairs imply that at state60 reading0, the cell immediately left
is0: the possible five-bit windows are exactly8,9,24,25. The unchanged source
rows are 60/0:0L45, 45/0:0R43, 43/0:0R51. Thus three faster253 moves and one
composed253 move have exactly the same control, head, and entire tape. All
eight radius-two local windows satisfying the two-zero guard were checked.

At every other row one composed move equals one faster move. From the common
blank start, each composed step therefore matches either one or three faster
steps, always with positive progress and without skipping a terminal state.
Consequently ZFC can prove, by ordinary induction using the finite certificate,
that composed253 halts iff faster253 halts. This is an unconditional
table-to-table statement. The full consistency calibration of faster253 is
inherited from the separately attributed source27 argument and was not
formalized again here. This bundle creates no new end-to-end Coq/Lean theorem.

The composition's exact bootstrap duration is312855. Its endpoint is
state33/head-17 and all178 one-cells exactly agree with both prior tables.
The frame contains marker-18, header23, primary physical registers
[0,2,0,0,0,0,5,0,0], all158 spare blocks, the two nonzero spares at indices2/8,
and an all-zero exterior on the bi-infinite tape. All253 working states remain
graph-reachable. The composition saves120 initial steps and ZERO working states.

The new table SHA256 is:
a5e0c60484e6873dc1a32121652606e2f3b2a2ce6046ef26847fd7a62bcfe212

The five changed rows from public253 are:
37/0: 0 R41 -> 0 R42
37/1: 1 R42 -> 1 R48
42/0: 0 R50 -> 0 R41
42/1: 1 R48 -> 1 R50
60/0: 0 L45 -> 0 R51

Two independently written check paths passed: compose_shortcuts.py generates
and checks the control; check_composition_certificate.py imports no generator
module, verifies the literal tables and the closed invariant, reconstructs
the entire target frame, and runs all three finite bootstraps. The ordinary
proof above, not the finite boot alone, supplies the unbounded table transport.

Result 2: arbitrary two-row state-fusion synthesis
------------------------------------------------

Existing searches retained either the deleted or retained state's rows, or
searched single incoming-edge rewrites. synthesize_local_rows.py considers
each of the1016 possible binary actions (write0/1, L/R, any of253 working
targets or terminal) independently for each row. An action is retained as
a proposal if, when substituted only for the first move and then followed
by the unmodified machine, it matches some positive original block on every
abstractly reachable input window. Intersections of the retained action sets
for two different states propose the two rows of one fused state.

This first stage is ONLY a proposal heuristic. A proposed fusion changes both
rows simultaneously and redirects every incoming edge. The final checker
runs the fully modified table literally, at every original window of BOTH
the removed and retained state. It requires positive progress on both sides,
control equality after the state map, head equality, and whole known-window
equality before either run reads outside the known cells. Terminal matches
may ignore tape/head. All other states match in one move after state mapping.
This yields a sufficient whole-tape blank-halting certificate when it passes.

Measured domains and results:

input       radius bound abstract pairs action/context checks proposals accepted
public253       5    32      102061          906367               528       0
public253       6    64      335369         1619990               528       0
composed253     6    64      333193         1609100               542       0

For public253,526 of528 final recipes use at least one action outside the
original two merged-state rows; for composed253,540 of542 do. This extends the
particular previously recorded row-copy families. It is not a claim of global
novelty for state minimization, and is not exhaustive over arbitrary paired-row
rewrites: the first-stage heuristic can omit jointly correct transformations.

The final simultaneous check is essential. For example, remove compact10,
retain21, and use actions 0R23 / 1R23. Both pass the one-shot detour filter on
public253. But on a zero window the assembled candidate alternates between
state21 at head0 and state23 at head1, leaving zeros unchanged. The original
from state10 writes a1 and leaves that neighborhood. Thus a detour that borrows
an original control cannot be silently reused after deleting that control.
This is a local prepared-window counterexample, not a claim about the altered
machine's actual blank-tape run.

Result 3: incoming-edge detour controls
-------------------------------------

synthesize_edge_bypasses.py tries each noninitial state as a deletion source
and permits every external entering row its own arbitrary action. To make
independently selected rows compose, its candidate blocks do not execute a
deleted state or another edited row before reaching a positive whole-tape
match. On both public253 and composed253 at radius6/bound64, no state has
a complete set of bypasses. The original-table experiment overlaps the
incoming reports' prior incoming-row search and is included as a control,
not as new work. The composed-table control has252 sources and355646
action/context checks; again zero complete deletions.

What these results do not establish
----------------------------------

No252-state blank-tape ZFC consistency machine was found. No global state
lower bound or universal impossibility statement was proved. An abstract
window may be unreachable in the true run, a match may need more cells or
steps, and a useful transformation may require simultaneous edits outside
the tested criterion. The synthesis ledgers are diagnostic evidence, not
proof-assistant theorems. The complete-frame bootstrap has a finite scope;
the explicit invariant argument establishes the separate unbounded transport.

Result 4: complete bounded two-row fusion search by unknown-row pruning
---------------------------------------------------------------------

The later exhaustive_fusions.cpp strengthens Result2 by eliminating its
one-shot proposal heuristic. For each unordered pair p<q of working states,
it removes p, redirects every target p to q, and permits q's two rows to be
ARBITRARY binary write/move/target actions. Start0 is mapped if removed.
Each row has1012 actions: 2writes *2moves *(252 retained working targets
+1 terminal target). HALTING ACTIONS ARE INCLUDED. Only deleted p is omitted
as a target, since its redirection to q gives an already-present action.
Retaining p instead of q yields the same family up to state renaming.

Thus each table has31878 unordered pairs and a formal domain of
32647662432 row-pair recipes. This number is the family covered by sound
pruning, not the number individually simulated to completion.

A partial candidate fixes one retained-state row and leaves the other
unknown. It stops immediately if that unknown row is requested. A bounded
failure that occurs before requesting it is independent of every possible
completion of the unknown row. Such actions can be discarded soundly.
Every combination of the remaining zero/one actions is checked with the
literal simultaneous mutation on every abstract window at BOTH merged
states. Original and candidate make positive progress, preserve the full
known tape/head/control after state mapping, and read no exterior cell.
An exact candidate loop before asking an unknown row cannot later produce
a new match, so loop detection is also sound.

All runs use radius6 (13 cells) and64 moves per side. The abstract reachability
construction admits both values of newly exposed exterior cells.

metric                              public253        composed253
abstract state/window pairs             335369             333193
unordered state pairs                    31878              31878
actions per synthesized row               1012               1012
formal recipe family               32647662432        32647662432
partial context evaluations          425869377          425389366
full simultaneous recipes               222780             227359
full context evaluations               7514660            7540469
certificates                                  0                  0

Each run took approximately38seconds. The per-pair TSVs record both surviving
action-domain sizes, full recipe counts, and certificate counts. Summaries
are exhaustive_public_r6_summary.json and exhaustive_composed_r6_summary.json.

test_exhaustive_pruning.py independently enumerates EVERY action-pair recipe
without pruning on five small machines. All7936 recipes agree with C++,
including all3768 positive certificates. The cases exercise halting actions,
start removal, cycles, empty/unreachable contexts, and partial-row pruning.
The test is a differential implementation check, not a proof-assistant proof.

The result is exhaustive only for this finite local-matching criterion in
the precisely defined fusion family. It does not prove semantic inequivalence
of rejected candidates or a state-count lower bound.

Reproduction, Python3.10+ and no third-party packages
---------------------------------------------------

From this directory:

python3 compose_shortcuts.py inputs/public253.tm inputs/faster253.tm --output-dir .
python3 check_composition_certificate.py inputs/public253.tm inputs/faster253.tm --dir .
python3 synthesize_local_rows.py inputs/public253.tm --radius 5 --steps 32 --output synthesis_radius5.json
python3 synthesize_local_rows.py inputs/public253.tm --radius 6 --steps 64 --output synthesis_radius6.json
python3 synthesize_local_rows.py composed253.tm --radius 6 --steps 64 --output composed_synthesis_radius6.json
python3 synthesize_edge_bypasses.py inputs/public253.tm --radius 6 --steps 64 --output bypasses_radius6.json
python3 synthesize_edge_bypasses.py composed253.tm --radius 6 --steps 64 --output composed_bypasses_radius6.json

For the stronger exhaustive family:

g++ -O3 -std=c++17 exhaustive_fusions.cpp -o /tmp/zfc_exhaustive_fusions
python3 prepare_exhaustive.py inputs/public253.tm /tmp/zfc_public_fusions.input --radius 6 --steps 64
/tmp/zfc_exhaustive_fusions /tmp/zfc_public_fusions.input exhaustive_public_r6 > exhaustive_public_r6_summary.json
python3 prepare_exhaustive.py composed253.tm /tmp/zfc_composed_fusions.input --radius 6 --steps 64
/tmp/zfc_exhaustive_fusions /tmp/zfc_composed_fusions.input exhaustive_composed_r6 > exhaustive_composed_r6_summary.json
python3 test_exhaustive_pruning.py /tmp/zfc_exhaustive_fusions --output exhaustive_pruning_differential.json

The executable and large generated input windows are temporary; the source
tables, generator, C++ source, differential check, and result ledgers are the
complete reproducibility inputs.

Source pins and attribution
--------------------------

ProveIt inspection pin:
61e77836565f63582561f54745f633d50efd9c7d

Public253, by mira-emmy from Mira-Cult's original machine, Jeff's verification,
and Andrew James Wade's framework:
https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm
SHA256 84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95

Faster253, existing source27 contribution, retained at:
https://github.com/VladimirReshetnikov/ProveIt/blob/61e77836565f63582561f54745f633d50efd9c7d/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/27-variant-machines-faster_253.tm
Review:
https://github.com/VladimirReshetnikov/ProveIt/blob/61e77836565f63582561f54745f633d50efd9c7d/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-152-source-27.md

The separate incoming shortcut is preserved at:
https://github.com/VladimirReshetnikov/ProveIt/blob/61e77836565f63582561f54745f633d50efd9c7d/docs/incoming/zfc_consistency_research_20261016.zip
Its Git blob is fed571ff08f2e78630dd5ce8b8b295b7f92c3718. Its title is
"A guarded three-step shortcut in the public253-state ZFC machine" within
experiments/public253/PROOF.md; its table SHA256 is
78dcbd5aa7709f349cb9c378f54909e316c27d448537cf2e9dce15811152c2a4.
It is prior input to this composition and is not claimed as a new discovery.
