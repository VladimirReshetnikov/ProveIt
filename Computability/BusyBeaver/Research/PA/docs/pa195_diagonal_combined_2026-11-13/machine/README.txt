PA195DC: diagonal AX emitter with the Combined controller
=======================================================

RESULT: 195 working states, two symbols, one two-way tape, all-zero input.
Start state 0. Working states 0..194. The separate halt label is 195.
Every working-state/read-bit pair has exactly one transition.

    python3 build_verify.py

This uses Python 3 and its standard library only. No search, solver, network,
or theorem-prover installation is required. Run without Python -O.

    python3 build_verify.py --export

also rebuilds derived source, startup, fold, and runtime certificates.
Both commands verify the complete supplied machine bytes; they never rewrite
machine.tm, machine.native.tm, grammar.json, or folds.json.

Dense literal SHA-256:
e5cc1b2cb374fa4342070e95d8bdfd60c1bb845e7a52d44857bdee937bba7938
Native literal SHA-256:
af14a91d29da1acba0e47067fb3cea6a0c7fc6441b012e85c52840a3a0486f04

What changes
------------
The diagonal 191-token AX emitter and its seven contextual folds are unchanged
from the supplied PA195. The outer command controller implements the supplied
Combined196 transformation: Shift tests the cached head h=1 rather than the old sum t+h=1;
successful MP transfers its conclusion from D to H and clears D, rather than
pushing a dummy zero and then copying D. The literal implementation changes six
transitions in native coordinates, listed in verification.json and build_verify.py.
This changes the source algorithm and the blank execution, not just state names
or association of the same source tree.

The compiled source has 3676 primitive operations, compared with 3700 in its
PA195 parent. Exact initialization takes 57922 transitions, compared with 58154.
The source and physical table are new as a combination; the emitter and command
transformation separately are inherited and attributed in PROVENANCE.json.

Files
-----
machine.tm                 Complete dense binary table, start 0, halt 195.
machine.native.tm          Same machine in inherited native coordinates.
labels.json                Dense-to-native map, with halt last.
grammar.json, folds.json    Exact unchanged PA195 emitter and folds.
unfolded202.native.tm      Complete pre-fold machine with new controller.
source.json                All 3676 source sites and resolved successors.
source_binding.json        Exact old-prefix relocation and 15-row new tail.
local_fold_certificate.json All 28 simultaneous two-cell fold cases.
startup_certificate.json   Complete initialized tape, head, and control.
emitter_tokens.json        Complete 191-token AX word.
verification.json          Full deterministic verification receipt.
build_verify.py            Reproduction and certificate checker.
baseline195/               Original supplied PA195 package, unchanged except
                           removal of transient Python cache files.

Verification and proof status
-----------------------------
The checker first reconstructs the supplied PA195 machine from its own grammar,
folds, and pinned vendor files. It verifies its exact table, source binding,
emitter identity, all symbolic contracts, and complete blank initialization.
It then applies only the six documented controller transitions and two source
DAG substitutions, and checks both source CFG resolvers independently.

All 4784 new symbolic source-step contracts pass for both the unfolded and
folded tables. The arithmetic-box rows are checked unchanged. Those symbolic
contracts treat unary register values as parameters and use the inherited
register-engine lemmas. They are not finite numeric test samples.

The seven folds have 28 complete local cases on two tape cells. Their positive
simulation durations are 1, 3, or 5. Each case checks the whole-tape boundary:
all cells outside the two inspected positions are arbitrary and unchanged.
Together with all incoming-history checks, these give the finite certificate
for the ordinary mathematical global halting-preservation argument.

The accompanying research report provides the logical consistency argument
and the uniform arithmetic proof that the changed command interpretation
recognizes exactly refutability in PA. This packet does not claim a newly
kernel-checked Lean/Rocq proof of the full PA consistency biconditional.
In particular, executing the Python checker alone is not a proof of every
mathematical calibration lemma or its internal formalization in PA.
