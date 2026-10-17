STRUCTURAL COMPILER EXPERIMENTS: SCOPE AND PROOF BOUNDARIES

Source baseline
---------------
Repository: VladimirReshetnikov/ProveIt
Pinned commit: 43026ff42f0939f09b9e95495248cfadcad38e38
Baseline: candidate-permutation252/zfc_permutation252_old.tm
Baseline SHA256:
939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713

The original machine has 252 working states, a separate halting label 254,
blank start label 64, and register-frame entry label 96. State counts in these
experiments exclude the halting label. Numeric labels are not state counts.

Result
------
This investigation did not find a machine with fewer than 252 working states.
The source-level negation identities yield correct modified-source machines
at 261 or 262 states under conservative fresh emission. The subsequent transition-fold search then
reduced the direct-negation machine to 255 states. The shifted preadd and
add-eight variants also pass the same six-fold seed at 255 states.

The 203-node decoder with maximum zero-run six is an abstract source result,
not a validated smaller Turing machine. Its tested emitted tables fail
instruction contracts. Likewise, the 201-node direct-negation source DAG is
not a 201-state Turing machine. A conservatively repaired emission for that
source needs 266 states for its runtime contracts at gap 44+n, n>=0; it has no
established blank-start bridge. A literal search of 3,000,000 blank steps found
no qualifying later frame for that exploratory table. This finite observation
does not establish what happens later.

What the runtime checks establish
--------------------------------
For each source instruction path, and separately for the zero and nonzero
branches of every decrement, the strict affine checker derives the prescribed
successor frame for every free gap parameter n>=0 and every register file
satisfying that named guard. It preserves the complete register marker, tape
exterior, and spare registers, and requires positive literal progress.

The proof rules use exactly the four original register-box excursion
contracts. The 55 protected transition rows remain unchanged. The checker is
ordinary Python symbolic reasoning code, not a new kernel
verification of the experiment. Its contract assumptions must remain explicit.

For the accepted fresh direct and shifted variants, a separate literal blank
execution reaches the same zero-primary-register frame after 82,552 steps,
with gap 40, all nine primary registers zero, and the recorded spare suffix.
The finite boot and unbounded instruction contracts serve different purposes.

Closed source rotations preserve sequential behavior because the rotated
blocks have no escaping break or continue. The arithmetic source rewrites
additionally require the Clean scratch-register precondition and the proof
that all changed negation calls satisfy it; see the accompanying theory artifacts.
No new formal end-to-end ZFC equivalence follows merely from these experiments.
Any final Con(ZFC) claim still requires the complete upstream calibration and
the modified-source semantic bridge. The main report states that boundary.

Why several promising source grammars fail to emit cheaply
---------------------------------------------------------
An old optimized entry can inspect tape bits preceding its nominal subtree.
It can also borrow a transition row nominally belonging to another subtree.
For example, old state 237 is the unique pure entry for old source node 92,
but unchanged source node 104 calls 237/1 through 183/1 -> L213 and213/0 -> R237.
Changing 237/1 as though only node 92 owned it breaks an unchanged decrement
of logical register 2. Thus neither identical subtree hashes nor purely
right-moving entry rows are sufficient conditions for safe entry reuse.

The maxzero-six search targets deletion of return-counter state 74. The accompanying
counter experiment identifies 36 failing baseline guards at 18 decrement sites
with seven trailing zeros. Rebracketing can eliminate the abstract zero-run
obstruction, but does not by itself justify the optimized emitter or the
transient tape behavior of the shortened dispatcher.

Negative search scope
---------------------
The ledgers certify the outcomes of the named finite recipes and bounded
random/beam searches only. They are not lower bounds on Turing-machine state
complexity. A runtime failure is reported with its first failing instruction;
an affine unknown-run failure can be checker incompleteness, while the recorded
wrong-register marking examples are substantive contract failures.

The incremental rotation search reuses a previous successful case only when
the path, operation, and decrement guard agree and none of the transition
rows read by that successful trace has changed. Determinism then preserves
the entire trace. A saved improvement receives the complete uncached check
and literal blank bootstrap as well. The random search is bounded; its ledger
records its seed/checkpoint and outcomes, not an exhaustive global search.

Reproduction
------------
Python 3.10 or newer is sufficient for the authored drivers. Set PROVEIT_SOURCE
to a checkout of the pinned commit containing the upstream verifier modules
and the SetTheory/.../27-...-strict_affine.py file. The default path used during
research was ../../source/ProveIt relative to this directory.

Examples from this directory:

  PROVEIT_SOURCE=/path/to/ProveIt python search_structural.py --mode baseline --allocation fresh --output reproduced-baseline

  PROVEIT_SOURCE=/path/to/ProveIt python warm_rotation_search.py direct_negation/fresh.json --limit 1 --output reproduced-direct

  PROVEIT_SOURCE=/path/to/ProveIt python warm_rotation_search.py shifted_negation/shifted-negation-preadd_fresh.json --limit 1 --fold-log accepted-folds-six.json --output reproduced-preadd255

  PROVEIT_SOURCE=/path/to/ProveIt python single_incoming_modified.py shifted_negation/shifted-negation-preadd_fresh.json --fold-log accepted-folds-six.json --output reproduced-preadd-helper

  PROVEIT_SOURCE=/path/to/ProveIt python large_gap_repair.py negation_minimize/best_28061_201.json --output reproduced-generic201 --boot

The accepted-fold files are compact derived seeds, not substitutes for the
accompanying exhaustive fold ledgers. Replaying a seed remains a candidate proposal
until the full runtime and bootstrap checks pass on its own source.

scope_summary.json summarizes all search branches. The delivery manifest
lists the curated drivers, node graphs, tables, and ledgers and their hashes.
Large intermediate candidate dumps and Python bytecode caches are omitted.
