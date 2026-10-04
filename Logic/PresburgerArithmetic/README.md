# Presburger arithmetic is decidable

This directory formalizes Cooper quantifier elimination for first-order
arithmetic over the integers with addition, order, equality, congruence, and
Boolean connectives. Multiplication is restricted to multiplication by an
integer constant, as required for Presburger arithmetic.

## Lean

The Lean development is an executable end-to-end decision procedure:

1. `Syntax.lean` defines affine expressions, divisibility atoms,
   quantifier-free formulae, and first-order formulae (universal
   quantification is the derived operation `¬∃¬`).
2. `NormalForm.lean` computes disjunctive normal form, including constructive
   negation of inequalities and divisibility atoms.
3. `Cooper.lean` proves the periodic residue and finite-interval lemmas at the
   heart of Cooper elimination.
4. `Elimination.lean` normalizes coefficients and proves one-variable
   elimination correct.
5. `Decision.lean` recursively eliminates every quantifier and defines the
   Boolean decision procedure `Formula.decideSentence`.

The advertised executable decision definition is

```lean
PresburgerArithmetic.Formula.presburgerArithmetic_decidable
```

and `Audit.lean` prints its axiom dependencies together with the central
correctness theorems.

Focused build:

```powershell
lake --dir Logic/PresburgerArithmetic/Lean build
```

## Rocq/Coq

`Cooper.v` gives an independent constructive proof of the decisive normalized
one-variable Cooper step. For a decidable predicate `P` periodic modulo a
positive `m`, and finite lists of lower and upper bounds, it computes whether

```coq
exists x, all_lower los x /\ all_upper his x /\ P x
```

holds. `cooper_finite_criterion` proves that this unbounded existential is
equivalent to a finite residue search (or finitely many bounded searches), and
`cooper_step_decidable` packages the resulting executable sum-type decision.
This is exactly the non-Boolean step iterated by the Lean quantifier
eliminator; the Coq development independently checks its mathematical core.

Focused check:

```powershell
coqc -Q Logic/PresburgerArithmetic/Coq PresburgerArithmetic Logic/PresburgerArithmetic/Coq/Cooper.v
coqc -Q Logic/PresburgerArithmetic/Coq PresburgerArithmetic Logic/PresburgerArithmetic/Coq/Audit.v
```

The decision procedures are executable and neither development uses `sorry`,
`Admitted`, or a custom arithmetic oracle. The Lean audit exposes only Lean's
standard logical axioms used by mathlib; the Coq audit is closed under the
global context.

## Related research reports

[`Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic`](../../Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/)
(batch 86 of the incoming reports; two of its sources pin commits
`a11efab09` and `3ad5f878c` and read this project's Lean and Rocq files)
constructs Polish models of Presburger arithmetic with continuous addition
on nonstandard Z-groups `D ×→ Z`, an affirmative answer to Glazer's
Question 2 as printed. It notes that the periodicity lemmas here — Lean
`periodic_interval`, `periodic_has_residue` and `cooper_finite_criterion` in
`Cooper.lean`, Rocq `periodic_shift`, `periodic_has_residue` and
`periodic_interval` in `Cooper.v` — are stated for the ordinary integers with
one-step periodicity, where they are correct, and that a version uniform over
models needs invariance under a whole subgroup `mG` (its
`pma:pr:ex:falseperiod` and `pma:pr:lem:finite`). This is a porting
requirement, not a defect. Its Parts III and IV (three more sources, pinned
at `0f95145cb`, `fa2f3e419` and `883e0b3b2`) read this project again:
`Formula.holds` in `Syntax.lean` and `holds_iff_quantifierEliminate` in
`Decision.lean` are stated for `List Int` valuations, so the semantic
theorem for an arbitrary Z-group would be a further formalization task, and
the finite-witness lemma needs invariance on cosets of `mG`
(`pma:lc:lem:cooper`). Its Parts VI–XII (batches 87, 89 and 90) cite this
project again, always as a route to a further formalization: Part VI's
formalization plan names its affine syntax, normalized Cooper step and
Lean decision procedure and says that transfer to abstract Z-group
semantics is a separate theorem; Part VII (`pma:nsp:`, stream evaluation,
exact continuity and truth-revision bounds for Presburger formulas over
nonstandard Z-groups) and Part IX (`pma:lcc:`, locally compact cones) read
`Syntax.lean` and `Decision.lean` and note again that `Formula.holds` and
`holds_iff_quantifierEliminate` are stated over `List Int`; Part X
(`pma:emb:`, elementary embeddings of lexicographic models) read only this
README and begins its proposed modules with the same coset-invariance
requirement; Part XII (`pma:gcm:`) gives a criterion for a Polish
Presburger cone to extend to a Polish group (continuous partial
subtraction), which does not touch this project's integer semantics.
Parts XIII–XVII (batches 92 and 93) do not read this project: Part XIII
(`pma:ord:`) classifies the Borel Presburger orders on `R × E` and, with
Parts IV, IX and XII, every uncountable locally compact Polish Presburger
model with continuous partial subtraction, and Part XVI (`pma:hbo:`) builds
Polish Presburger models from Borel orders on Hilbert spaces; both use only
the classical theory of Z-groups and leave this project's integer
semantics untouched.
**Nothing in that report is formalized**, and nothing in this project
depends on it.

The research report
[`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits`](../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/)
(batch 83) invokes Cooper's quantifier elimination, formalized here, for an
unexecuted second proof of its exact first-hit theorem; its own theorems are
not formalized.
