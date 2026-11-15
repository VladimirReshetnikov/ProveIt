LOW-LEVEL REDUCTION RESEARCH: EXACT INPUTS AND BOUNDED SEARCHES

Snapshot: VladimirReshetnikov/ProveIt
603c58ca3bd6bf3222fcfc4e308e6b079f65d573

RESULT

No machine with fewer than 194 working controls was established. This folder
documents completed searches supporting that candid outcome. The main report
supplies the new 194-state selector constructions and their direct relative
equivalence proof. No search failure below is a lower bound on consistency
machines or a proof that 193 controls are impossible.

CONTENTS

code/                  Portable Python/C++ search sources; no binaries.
inputs/                Exact primary, selector, positive-control and grammar inputs.
receipts/search_results.json
                       Machine-readable completed scopes, counts and observations.
receipts/stutter_positive.json
                       A positive witness for the variable-old-prefix criterion.
PROVENANCE.json         Source revision, primary identity, imported-code ancestry.
licenses/              Original notices accompanying reused source and data.

The primary native table has 194 working states, initial control 74, terminal
control 254, and SHA-256
e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54.
All search tables in inputs/selectors use this same native interface.
Every transition writes a binary symbol, moves one cell, and changes control.

REPLAY

Requirements: Python 3.10+, a C++17 compiler available as g++, standard libraries.
No network, Lean installation, repository checkout or third-party package is used.
Run without Python -O. From this directory:

    python3 replay.py

This runs the positive control and three small completed enumerations.
List all available finite jobs with:

    python3 replay.py --list

Replay all finite enumerations, retaining fresh outputs in a chosen directory:

    python3 replay.py --all --output /tmp/pa194-lowlevel-replay

The larger window jobs require more time than the quick default. Output timing
is not an acceptance criterion. Every reported integer count and empty survivor
list is compared to the frozen observation. The positive control must include
the particular two-old-step/two-new-step witness recorded in its JSON file.

The four optional grammar searches can be rerun as the exact recorded proposal
prefixes rather than by elapsed time:

    python3 replay.py --grammar --output /tmp/pa194-grammar-replay

These cover 36,325,019 proposals and may take tens of minutes when run sequentially.
They originally ran for 600 seconds each. The supplied replay-only optional
iteration argument stops at each recorded proposal count; it does not alter the
search mutations, scores or random-number stream. Accepted-move counts, best
scores and sub-194-hit counts are compared as well. Floating-point annealing
uses the platform's C++ standard library.

For the standalone arbitrary-exterior Python fold search, copy its three inputs
to a writable directory and invoke its explicit data/output-root argument:

    mkdir -p /tmp/pa194-local-fold
    cp inputs/pa194.tm inputs/pa194.labels.json /tmp/pa194-local-fold/
    python3 code/extended_local_fold.py 15 /tmp/pa194-local-fold

This replays 4,107 opposite-forced-context pairs. It writes its own JSON receipt.

MODELS AND EVIDENCE BOUNDARIES

1. Strict finite-context folds.
   The initial Python search uses the symbol just written by the predecessor,
   allows arbitrary exterior tape, and tests at most 15 replacement steps.
   Its accepted fragments must reach the exact projected old one-step endpoint.
   No successful fold was found.

2. Finite-window two-row contractions.
   joint_return_merge.cpp computes a sound finite window overapproximation of
   the primary machine's blank execution: a newly exposed boundary bit may be
   either 0 or 1. A least fixed point gives the tested contexts. It then removes
   one control, synthesizes both rows of the retained control, permits repeated
   visits to that control, and tests the exact old one-step endpoint without
   reading outside the window. This inherited strict search enumerates working
   targets only. None of the recorded primary or selector runs found a survivor.
   Its small robustness correction handles controls absent from the abstract
   reachability set before an optional externally supplied context set is read.

3. Variable-old-prefix stuttering contractions.
   stuttering_merge.cpp additionally accepts equality with any positive old
   prefix up to the recorded old_bound. It includes direct halt targets and
   ignores terminal tape decorations once both runs halt. Both executions must
   stay within the window until they meet, apart from their final head move.
   It covers the primary and the selected composite at radius 8, up to 32 old
   steps and 160 replacement steps; all eleven single/composite selector inputs
   were also tested at radius 6, up to 16 old steps and 120 replacement steps.
   These are completed finite syntheses, not unbounded equivalence decisions.
   The positive control genuinely requires a two-step old/new matching segment.

4. Three-control shared selectors.
   shared_selector_search.cpp examines all 116 disjoint pairs of the 16 eligible
   two-control families listed in selector_pairs.txt. Eligibility means a forced
   left witness 0 or 1 on every entry and exactly one common outgoing row. It tries
   both retained labels in each family, either recycled selector label, all four
   tag assignments, and all writes, directions and working-or-halt targets for
   the selector's two rows. The completed radius 4/120-step run checks 3,712
   structural configurations,4,109,696 single-row proposals and 8,016 joint row
   combinations. The exterior tape is arbitrary. It found no 193-state table.

5. Grammar searches.
   The baseline adds occurrence-specific reassociation to global shared-node
   rotations. The three further experiments exchange the antecedents in the
   third and/or fourth numbered seed; the exchange is the pure implicational
   identity P->(Q->R) iff Q->(P->R). They also permit independent bijective
   parameter renaming within the six numbered seed blocks. The best objectives
   were 60 for the baseline and 62, 62, 65 for the changed emitters. With 134 fixed
   controls these correspond to 194, 196, 196, 199 in the compiler objective.
   These numbers are search scores, not newly verified consistency machines.
   No completed physical source-contract audit is asserted for the changed
   grammar outputs. The objective's scanner constraints remain a screening model.

The tempting first-seed contrapositive was rejected and is excluded from this
package: treating the distinguished falsity code as ordinary Boolean false
would silently assume explosion, which that replacement can lose in the actual
primitive implicational calculus. Interrupted seeding experiments are likewise
not used to support an exhaustive negative statement.

WHY THE STUTTERING ACCEPTANCE CRITERION IS USEFUL

At an affected old control the certificate would consume u old steps and v new
steps, with 1<=u<=old_bound and 1<=v<=new_bound, and reach the same projected
configuration. Outside the affected controls the original one-step correspondence
remains. Exact window equality plus the prohibition on reading outside the window
gives equality on the full arbitrary exterior tape. Positive progress on both
sides composes these segments along the blank executions, with linear witness
rescaling. The context fixed-point invariant is finite. Thus an actual accepted
certificate of this form would be suitable for elementary arithmetization in
iPRA. This describes the finite model being searched; it is not a new kernel
theorem or an assertion that every possible contraction has this form.
