Alternative 196-state binary machine
====================================

Status: a verified physical variant with the SAME state count as PA196.
This is not a construction with fewer than 196 states. The Python symbolic
checker passes; the supplied candidate-specific Lean files are generated
sources and have not been built as part of this subtask.

Base repository:
  https://github.com/jamesyc/BusyBeaver
Base commit:
  407cdc356f6b586635e71ac92be394255f4bfea4

Machine convention
------------------
One two-way infinite tape, alphabet {0,1}, initially all zero.
Each transition line is: state read write direction next.
Directions are L or R. There is one row for each working-state/symbol pair.

alternative196.tm: working labels 0..195, initial state 0, root state 75,
                  halt label 196 (which has no outgoing transitions).
alternative196.native.tm: corresponding sparse working labels,
                  initial state 74, root state 84, halt label 254.
labels.json: literal index -> sparse label, including the halt label last.
The unique halting row in literal labels is (63,1,1,R,196).

SHA-256 of alternative196.tm:
aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95

Reproduce the physical checks
-----------------------------
Run with Python 3.10 or later, with no external Python packages:

  python3 verify.py

The checker verifies all 392 rows, the native/literal correspondence, all
46 rows of the 23 engine states against engine_rows.json, the 58,154-step
blank-tape startup, and 4,959 symbolic instruction contracts. The symbolic
contracts cover every one of the 3,812 source sites, with both branches at
all 1,147 decrement sites. The symbolic gap is n+48 for arbitrary n >= 0.
The complete register file is symbolic, with at least ten registers and the
specified zero/nonzero assumption when a decrement branch is checked.

The symbolic executor is an independent Python port of M6/Runtime.lean.
It uses the four unchanged register-file excursions proved by M6/Native.lean.
The checker is not a Lean kernel proof and does not independently re-prove
those register-file lemmas. Its output must not be described as a full
formal verification of the PA consistency equivalence.

Observed results
----------------
Working states: 196. Rows: 392. Source sites: 3,812.
Longest source path: 36, compared with 38 in the base machine.
Symbolic contracts: 4,959; maximum 497 abstract steps, total 1,539,117.
The base machine has maximum 515 and total 1,619,679 under this same checker.
These abstract counts include bookkeeping/oracle steps and are not literal
Turing-machine running-time bounds.

Startup ends after exactly 58,154 literal transitions, in sparse root 84,
with absolute head position -2 and 66 one cells. This endpoint was also
compared cell-for-cell with the base machine. The final physical register
file is [0,0,0,0,0,0,2,0,0] followed by 26 one-valued spare registers.

Construction and logical transport
----------------------------------
The body of AX retains the same 201 macro tokens, except for permuting the
six independent axiom heads. Their old bottom-to-top push order 1,2,3,4,5,6
becomes 1,2,3,5,6,4. The saved top, generalization, rho8, final guarded gate,
and the nine-item stack count remain the same. All formula constructors,
axiom schemas, and parameter meanings remain the same.

The binary association of the AX macro sequence is changed. It still has
68 distinct internal nodes, and six predecessor-sensitive folds reduce the
body to 62 reader states. The remaining 134 physical states are retained.
grammar.json records the association; summary.json records the six folds.

At the command-calculus level, the set of axiom instances is identical.
Soundness is unaffected by their order. For completeness, adjust the old
head-selection words. If j is the old position counted from the top,
the new positions for j=1,2,3,4,5,6,7 are 2,3,1,4,5,6,7. The seventh item
is rho8. Head parameters are unchanged. This finite permutation gives a
primitive-recursive translation of proof-command certificates in both
directions. It therefore transports any established PA-internal correctness
theorem of the base construction once the physical simulation and startup
are formalized for this literal table. This packet does not claim to supply
that complete PA-internal formalization.

Lean integration assessment
--------------------------
Program.lean, Table.lean, Literal.lean, and Conjugacy.lean are candidate
replacements in an isolated checkout of the pinned base repository.
The table keeps the engine's sparse labels, root 84 and halt 254. The
physical source-site count is still 3,812; all paths still satisfy the
existing <=38 theorem statement. Consequently the generic RuntimeContracts,
PrimitiveSimulation, CompilerCorrectness, CheckCoverage and 239 blocks of
16-site coverage statements can be rebuilt without changing their generic
proofs. The existing physical Startup trace has the same configurations
and endpoints; it should be rechecked against the new Literal table.

Rebuilding this physical layer is modest relative to the full repository,
and uses its existing Std-only proof infrastructure. Do not expect the old
AXEffect and proof-command compiler theorems to compile unchanged: their
explicit ordered lists and head-selection indices need the permutation
above. The arithmetic trace construction also must be bound to the new
literal rows before any full internal-equivalence claim is made.

File notes
----------
Program.lean defines the exact source tree, sites.json and instructions.json
provide independently regenerated data, and verify.py recomputes the data
from Program.lean rather than trusting those JSON files. engine_rows.json
is frozen base-machine engine data. The root repository's MIT license is
retained in LICENSE for the adapted source and proof material.
