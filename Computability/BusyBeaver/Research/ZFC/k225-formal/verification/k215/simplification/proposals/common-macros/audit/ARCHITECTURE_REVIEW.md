# Architecture review: shared macro proofs with exact graph footprints

Reviewed snapshot: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

## Main finding

The maintained Rocq files `ProgLibDom.v` (781 lines, 38,002 bytes) and
`ProgLibPerm.v` (780 lines, 37,951 bytes) have identical source bodies after
removing nested Rocq comments, consistently renaming the candidate module and
program, and normalizing whitespace. The result is not a merely approximate
text-similarity observation: the audit script asserts exact equality of the
normalized strings and records the input hashes.

The corresponding *literal Rocq* DAGs have 484 and 487 nodes. Only four shared
indices differ: 139, 141, 147, 471. The additional target indices are 484, 485,
486. The largest closed agreeing set contained in the source index range has
466 nodes. Its complement is:

```
0, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
236, 467, 468, 469, 470, 471
```

Every one of the 58 library lemmas whose statement contains a literal `ENode`
mentions only nodes in that agreeing region. There are 53 distinct roots in
those statements, and their complete descendant closure contains only **89
nodes**. Thus the fixed macro contracts need an 89-node graph interface, not a
new proof of the entire candidate program.

The audit parses the actual maintained Rocq tables, independently checks their
equality with the corresponding source JSON, and computes the region from the
literal children. It rejects a changed increment at node 188 and a footprint
with that required child removed, while allowing a change at root 0 outside the
macro footprint. These are finite audit checks, not kernel proofs.

## The reusable theorem

For programs `p`, `q`, let `S` be a set of node indices. An edge is inside `S`
when it is primitive or is `ENode n` for `n` in `S`. Assume for every `n` in `S`:

1. `p.nodes n = q.nodes n`;
2. both children of that pair are inside `S`.

Then, for every inside edge `e`, every initial register file `R`, every exit
`x`, and every final register file `R'`,

```
run p e R x R'  <->  run q e R x R'.
```

Proof: induct on the finite big-step derivation. Primitive cases are identical.
At a node, use the equality of its children, apply the induction hypotheses to
the needed child runs, and rebuild the same constructor. In the `continue 1`
case, the reentered node is still in `S`, so the induction hypothesis for the
recursive node run applies. Reverse the roles of the programs for the other
direction.

This argument requires neither termination of arbitrary runs, nor a syntactic
acyclicity claim, nor an ordering on node indices. It preserves all exit tags
and the complete register file. These strengths matter: a theorem only about
halting would not transfer the macro contracts consumed by `L2RootPerm`.

The same interface can admit a semantic contract at a changed node instead of
literal equality. Lean already has that more general form in `RMTransfer`.
The new Rocq transport prototype should be described as a port/completion of
that architecture, not as a newly invented mathematical principle.

## How to obtain actual proof deduplication

Simply replacing `ProgLibPerm` by imports of the entire 217 development can
reduce one file while increasing the K215 dependency closure. Do not count
this as an endpoint proof-size saving.

The intended production refactor is:

1. Share the `St` record, register updates, approximation relation, generic
   structured semantics, sequencing, expansion and loop rules in one module,
   with the program explicit where required.
2. Keep a canonical macro implementation containing the 89 required node
   equations. Prove the macro contracts once. Equivalently, parameterize the
   macro library by these 89 equations.
3. For each concrete DAG, prove its `MacroGraph` gate by finite evaluation,
   then transport the 58 contracts. Keep the old API names as small wrappers
   where downstream scripts need them.
4. Keep AX, dispatch and root proofs candidate-specific. Their root nodes lie
   outside the footprint, and the programs intentionally differ there.
5. Update the generators and verify that regeneration reproduces the proposed
   wrappers. Then rebuild the unchanged exact endpoint and inspect its
   assumptions.

The 89-node closure is the least forward-closed set containing the 53 roots in
the scanned theorem statements. It is not claimed to be a semantic lower
bound on all possible implementations of these macros. Nor do the current
measurements establish the final line saving of an unimplemented common
library: only the duplicate source size and the precise interface size have
been measured.

## Prior proposal overlap

`verification/k215/simplification/proposals/k215-simplification-3/rocq/CFG_REPORT.md`
already identifies an absent Rocq whole-node replacement theorem when discussing
two increment commutations. It explicitly distinguishes that missing theorem
from the Lean `RMTransfer.Closed` implementation. Its `REPORT.md` also recommends
separating generic machinery from the 780-line `ProgLibPerm` fork. The useful
advance here is a checked generic transport component together with the exact
Dom-to-Perm binding and the independently computed 89-node macro interface.

The recent main branch has already adopted the shared implication core, shared
derived rules, transitive-container factoring, source certificate normalization,
and the AX macro-word pattern. The 217 AX-word and generalized enumerator commits
are `ab6ceabe32eefb196d81154d0cb3a811ed9a38a1` and
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`. These should be acknowledged as
existing work rather than proposed again.

The last "Open" list in the proposal directory's README is historical: some
items listed there are already adopted by later maintained checkpoints. The
phase-14 README and the maintained source are better evidence of current state.

## Endpoint and trust boundary

The repository's verification record describes the checked statement as

```
Halt(K215, blank) <-> ZFC has a finite derivation of falsity.
```

Negating it gives the nonhalting/consistency equivalence, without taking
consistency as a premise. The maintained record explicitly distinguishes these
external proof-assistant theorems from an internal PA proof or a derivation
encoded in ZFC's own proof syntax. A refactoring report should preserve that
distinction.

The original Rocq endpoint closure has 237 sources (195 pinned reference plus
42 K215 files). Its four sparse/dense endpoint dependency reports are closed;
three imported utility axioms listed by the global `coqchk` context are not
endpoint dependencies. Lean's maintained phase-14 endpoint has 178 project
modules and preserves the profile `propext`, `Classical.choice`, `Quot.sound`.
These are repository-reported previous endpoint checks, not builds performed
by this source-data audit.

## Reproduction

```
python3 audit_macro_footprint.py /path/to/ProveIt > macro_footprint.json
```

The script uses only the Python standard library and `git rev-parse`. It does
not execute repository generators. The output includes all six input file
hashes, the observed snapshot, exact root and footprint counts, all 58 lemma
names, and explicit validation limits.

## Source anchors

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMTransfer.lean`: existing Lean
  `Closed`, `run_transfer`, `closed_of_contract`, `contract`.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Perm.lean`: existing closed-set
  transfer of the unchanged macro contracts from the older DAG.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/ProgLibPerm.v`.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/217/ProgLibDom.v`.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md`.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase14/README.md`.

## Subsequent component implementation

The Rocq contributor has now implemented the canonical 89-node program,
retargeted the complete arithmetic macro library to it, proved finite bindings
to both literal programs, and supplied all 58 concrete 215 contract adapters.
The independent review of those final bytes is `ROCQ_COMPONENT_REVIEW.md` with
`macro_component_review.json`. The 89-node analysis is therefore no longer
only a proposed decomposition. Generic-utility compatibility, production
integration and a full endpoint rebuild are still outside this component.
