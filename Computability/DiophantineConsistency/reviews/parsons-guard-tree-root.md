# Positive Boolean guard trees and their structural measure

`ParsonsGuardTree.Tree` extends the earlier prefix descriptor to finite positive
conjunctions and disjunctions, with universal prefixes and Σ₁ leaves. It is
stable under term rewriting. For a context whose sides carry descriptors,
`choose` either certifies the entire projected side as Σ₁ or identifies an
actual universal, disjunction, or conjunction occurrence.

The additive logical-node count `nodes` is unchanged by rewriting; the sum over
side entries strictly decreases when a universal is opened, a disjunction is
split into both disjuncts, or either branch of a conjunction is selected. This
corrects a crucial measure issue: Foundation's ordinary `complexity` is maximum
depth, whose sum need not decrease on disjunction splitting. The earlier
universal-only recursion remains valid with that earlier measure.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`; the
standalone rewriting-invariance proof for the node count uses only `propext`.
The [16-file replay manifest](parsons-guard-tree-replay/FILES.json) has SHA-256
`10590d59ed2f6dc1f6ec4100504eba6ebd9fe13453278a11fd601b895b2a447d`.
The direct `ParsonsGuardContext` source hash
`b99064b9dcb6bfcaa28e7ee4386dcb5f7ff7c3990beaeb7c0854feca4e6a266b`
matches its frozen snapshot, and its object hash is
`9e020252008aef0a2f8b056da37c5e7319b7de6c1c191811fb75c50a9c41343b`.
Earlier providers and Foundation/Mathlib are an inherited boundary, not a
fresh transitive source audit.

Tree descriptors are hypotheses, not yet constructed for every Π₂ formula;
bounded-quantifier normalization and the global derivation induction remain
open. This file alone does not prove the conditional counterexample case,
conservation, or the PRA-provability target. The HA theorem for the maintained
14-variable PDF equation is complete separately.

A third independent replay at `/tmp/parsons-guard-tree-build-u8xku09l`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
