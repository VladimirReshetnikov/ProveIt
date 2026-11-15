PHYSICAL REDUCTION RESEARCH: NO ACCEPTED SUB-194 MACHINE
======================================================

This directory is a reproducible research supplement. Its two 193-state
tables must NOT be presented as successful blank-start consistency machines.

  runtime193.native.tm
    The inherited 193-state execution core. It lacks an accepted blank
    initializer. Its state count does not meet the problem's full specification.

  REJECTED_merge1_3_193.native.tm
    A rejected quotient with a short, proved blank-start escape to the left.
    Native start is 74 and halt is 254. It cannot provide the intended
    nontrivial consistency encoding. See the explicit certificates below.

All physical experiments in this supplement use the original PA194 from
Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13.
It is reconstructed from unfolded201.native.tm and its seven folds.
The filename primary194.native.tm refers to that earlier PA194 input,
not the new PA194FW or H5XS machine. Its native SHA256 is
e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54.

All inputs are bound to ProveIt revision
883da8d55452ea097910ed2509a1eefc833ce292. PROVENANCE.json identifies input
paths, archive members, and machine hashes. Upstream licenses are retained.
No end-to-end Lean or iPRA consistency theorem is supplied here.

1. Arithmetic-state identifications
-----------------------------------

search_runtime.py screens all 253 unordered pairs among the 23 designated
arithmetic-box controls. For each pair, it takes each of the four choices of
which original control supplies the retained 0-row and 1-row, redirecting all
targets of the removed control. This is 1,012 proposals, with duplicates
possible when original rows coincide.

The initial physical filter comprises 135 explicit arithmetic excursions,
covering marking, increment, and zero/positive decrement. Sixteen proposals
survive this finite filter. check_runtime_merges.py checks the source outcomes
with the appropriate renamed arithmetic interface; none is accepted by that
affine source checker. A checker failure alone is not a proof of machine
inequivalence. The following proposal has a separate literal rejection.

Delete native control 1, redirect every target 1 to 3, and retain the old
control-1 transition for symbol 0. The retained control has

    (3,0) -> (0,L,3),    (3,1) -> (1,L,2).

From actual blank start 74, the rejected machine reaches after 23 steps

    state 3, head -5, complete one-cell support {-3,1,3,4}.

Every cell at or left of the head is zero. Induction proves that the
0-L-self-loop leaves the tape unchanged and moves left forever. This is a
general nonhalting argument after a finite prefix, not a long-run guess.

The finite prefix and this elementary invariant can be formalized using
quantifier-free induction in iPRA. Consequently, if PA is consistent, the
rejected machine cannot have the requested iPRA-provable equivalence with
Con(PA): such an equivalence together with its provable nonhalting would
prove Con(PA) in iPRA, and hence in PA, contrary to the second incompleteness
theorem. This is a conditional metamathematical rejection of the requested
provability property, not a claim to have proved Con(PA). The literal replay
is supplied; this supplement does not supply a Lean formalization of it.

There is also a failure of its advertised source simulation on a generic
well-formed site 0 frame. Start in native 84, head 0, with complete support
{-1,48} union {50,52,...,68}; this is source path 000000 and ten zero-valued
register blocks. The original PA194 input table halts after 1,003 transitions. The
rejected quotient reaches a leftward zero ray after 101 transitions. This
second test is a generic source-frame counterexample; the frame is not
asserted to occur on the original PA194 machine's blank execution.

The three *_physical_counterexample.json files record every literal row
of the finite prefixes and the complete tapes. verify_counterexample.py
reconstructs the tables, replays the rows, and checks the final ray invariant.

2. A larger initializer-repair pool
---------------------------------

The inherited core identifies native 301 with 88 and sets

    (88,0) -> (0,L,51),    (51,0) -> (0,R,122).

The source-frame behavior is the inherited research result; startup remains
the obstruction. In the original PA194 initializer, (51,0) must sometimes lead to
the old (16,0) write-one operation on a still-blank cell. The shared core's
replacement instead enters the source-selector route. From blank 74 its
first problematic use has head 12 and complete support {-3,1}; the altered
run subsequently reaches the rightward write-one loop at 35 with no marker
to its right.

The latest prior pool contained 346 proposals:327 outside the designated
BOX partition, plus 19 speculative arithmetic edits. This supplement inspects
the partition more finely. Six rows designated BOX are absent inside the
four arithmetic excursions and are constrained by the surrounding source
control: (3,0), (16,0), (16,1), (40,0), (60,1), and (113,0).

search_boundary_edits.py checks all possible replacements of these rows
against every affected affine source outcome. search_box_edits.py also
screens replacements of the remaining arithmetic rows by explicit physical
excursions. check_box_edits.py runs the source check; check_box_extended.py
rejects false positives that inspect a left boundary assumed blank by the
initial physical filter. In particular, four superficially promising edits
to (60,0) fail when the immediate left boundary bit is 1.

The union adds 18 proposals to the prior pool, for 364 total. These proposals
are research candidates: the mixed inherited pool includes speculative
edits, and individual checks are not certificates that arbitrary combinations
preserve semantics. No such assumption is used to report a physical hit.

3. Exact scopes and results of startup screens
---------------------------------------------

The frame recognizer compares the whole finite tape support, allowing any
of the 20 source frames at sites 25 through 44, arbitrary register values,
arbitrary translation, header gap at least 48, and a nonempty finite spare
list. A hit would still require a valid source seed and proof of every edit.
There were no hits, even under this permissive physical criterion.

New two-edit pairs, requiring at least one of the 18 new edits:

    eligible different-row pairs               6,312
    initial states per pair                       193
    runs                                    1,218,216
    literal transitions                    17,287,738
    halts                                      10,161
    outward-ray classifications             1,208,018
    bounded runs                                   37
    complete frame hits                             0

The fuel is 200,000 transitions; absolute head displacement is below 20,000.
new_pair_result.json and new_pair_hits.jsonl retain the results.

A separate causal depth-three screen explores edits only at rows actually
encountered by the current partial proposal. Monotone zero-reading outward
cycles contribute all their cycle rows, because editing a later cycle row
can destroy the ray. This prunes irrelevant edit orderings without claiming
to resolve a run beyond its finite bound.

Native start 74 completed its causal depth-three search:

    distinct edited-machine runs               24,839
    literal transitions                   998,488,305
    outward-ray classifications                19,740
    bounded runs                                5,099
    complete frame hits                             0

All 193 working controls were then examined as initial states. The other 192
starts received a 5,000,000-transition search allocation each (a currently
executing run can overshoot that allocation). Including the completed 74
search, the totals are:

    distinct edited-machine runs               49,454
    literal transitions                 1,892,213,633
    halts                                         484
    outward-ray classifications                39,309
    bounded runs                                9,661
    complete frame hits                             0
    starts whose allocation was reached           177

The complete per-start results are in causal_all_summary.json and causal_all/.
The 177 capped starts and 9,661 bounded runs are explicitly unresolved. A
bounded run, an exhausted search allocation, or failure to match one of 20
frames is not a proof that no valid initializer exists. None of these screens
establishes a 194-state lower bound, a global minimality theorem, or the
impossibility of a different 193-state consistency machine.

4. Reproduction
---------------

Python 3.10+ and a C++17 compiler suffice. Run without Python -O. No network,
repository checkout, external Python packages, or proof assistant is required.

Quick exact rejection certificate:

    python3 verify_counterexample.py

Arithmetic and source screens (about a minute on the original environment):

    python3 search_runtime.py
    python3 check_runtime_merges.py
    python3 search_box_edits.py
    python3 check_box_edits.py
    python3 check_box_extended.py
    python3 search_boundary_edits.py
    python3 build_bootstrap_pool.py

New two-edit startup screen:

    g++ -O3 -std=c++17 new_pair_startup.cpp -o /tmp/pa_new_pairs
    /tmp/pa_new_pairs runtime193.native.tm expanded_edits.tsv \
        templates.tsv 200000 /tmp/pa_new_pair_hits.jsonl

Causal depth-three screen from 74:

    g++ -O3 -std=c++17 causal_startup.cpp -o causal_startup
    ./causal_startup runtime193.native.tm expanded_edits.tsv templates.tsv \
        200000 3 74 2000000 /tmp/pa_causal74_hits.jsonl > causal3_result.json

Capped all-start extension, retaining the completed 74 result:

    python3 run_causal_all.py

The scripts use only files in this directory. Elapsed times vary; all discrete
counts are deterministic for the stated scripts, inputs, caps and traversal
orders. The C++ executables are not distributed; build them locally as above.

5. Interpretation
-----------------

The sharp mathematical lesson is that a hardware row may simultaneously
serve a register operation, a source-path selector, and blank initialization.
Correctness on arithmetic entry frames does not authorize quotienting that
row globally. The explicit 23-step counterexample makes this distinction
checkable. The new bootstrap screens broaden a previously restricted search
but leave the state-count target open.
