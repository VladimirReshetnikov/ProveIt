# Two further structural proof simplifications

Pinned source commit: `efa64ca941cdae37bb6f7fc5093ae8bb69296ca3`.

## S1. Use the diagonal invariant to remove helical integer induction

**Exact target:** `WangTiles942HelicalQuotient.row_zero_of_helix`, lines 22 onward in the pinned `Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HelicalQuotient.lean`.

The old proof treats positive and negative integer times separately. Both branches reconstruct the same invariant, `x+w*t`. Fix the requested `(x,t)` and define

`f(s) = T(x+w*s,t-s)`.

The helix law makes `f` periodic with period one. The existing `Function.Periodic.sub_int_mul_eq` theorem at integer point `t` and multiple `t` gives `f(0)=f(t)`, exactly the target. The candidate is:

```lean
  let f : ℤ → α := fun s => T (x+w*s) (t-s)
  have hp : Function.Periodic f 1 := by
    intro s
    dsimp [f]
    convert hhelix (x+w*s) (t-s) using 1; congr 1 <;> ring
  simpa [f] using hp.sub_int_mul_eq (x := t) t
```

This applies to every integer width `w`, including zero and negative widths. The codomain is arbitrary. No positive-width, vertical-period, nonempty finite quotient, or machine-run premise is added. Integer iteration has been discharged by an existing library theorem; the result stays theorem-driven.

The conceptual improvement has an exact stronger formulation, proved in the standalone kernel:

```lean
(∀ x t, T (x+w) (t-1) = T x t) ↔
  ∃! F : ℤ → α, ∀ x t, T x t = F (x+w*t)
```

Here `F(z)=T(z,0)`, and uniqueness follows by taking `t=0`. Conversely, every map of `x+w*t` is helical because `(x+w)+w*(t-1)=x+w*t`. This optional factorization theorem explains the geometry and can become an interface if another client needs it. It is not necessary to add it to obtain the measured saving: the existing theorem can use the six-line replacement directly.

**Measured delta:** the full module shrinks from 147 to 137 physical lines, a net removal of 10. No helper is added to the maintained source.

**Novelty:** full-corpus searches found no earlier proposal of this helical diagonal pullback, `row_zero_of_helix`, `sub_int_mul_eq`, or its factorization. The previous interval propagation and finite-invariant predecessor ideas concern different induction schemes. The earlier suggestion of an aligned-cell equivalence also does not supply this integer-plane invariant. This is a new proof of an unchanged theorem, not a new finite quotient construction.

**Validation:** the exact statement/body and the unique-factorization theorem compile in `StructuralKernels.lean`. Both use only `[propext, Quot.sound]`. The complete tile-dependent module has not been rebuilt; its patch is a proposed integration edit. The exact theorem needs only the same periodicity/ring facts already present in its imports. Do not label the full helical patch as independently module-compiled.

## S2. Eliminate deterministic function-valued existential witnesses directly

**Exact targets:** `Rep.compose` in `ComposeRepresentation.lean` and `GraphRep.composeDirect` in `DirectComposition.lean`.

After the earlier assignment-naturality and finite-block APIs have normalized the representation, these proofs still reach, respectively,

```lean
(∃ a : Fin n → ℕ, P a ∧ ∀ i, a i = f i v) ↔ P (fun i => f i v)
```

and

```lean
(∃ a : Fin n → ℕ, v none = f a ∧
  ∀ i, a i = g i (v ∘ some)) ↔
    v none = f (fun i => g i (v ∘ some))
```

Each old tail manually opens the existential, builds a function equality by `funext`, substitutes it, and reconstructs the canonical function in the converse. The entire tail is a standard equality-existential simplification:

```lean
  simp only [← funext_iff, exists_eq_right]
```

The first rewrite identifies pointwise equality with equality of the whole function. The second substitutes the uniquely specified function into the predicate. The same proof handles `n=0`; no inhabited-index or positive-arity premise is introduced.

**Measured delta:** 71 to 66 lines in `ComposeRepresentation.lean`, and 77 to 72 in `DirectComposition.lean`: 10 physical lines removed in total. There is no additional helper in the maintained code; `eliminate_function_witness` in the standalone kernel is explanatory only.

**Novelty:** prior finite-witness splitting deals with a function on `Fin(m+n)` versus two independently chosen witness blocks. Assignment naturality deals with variable renaming under evaluation. This proposal applies only after those obligations have disappeared: the remaining existential is an already determined *function* whose pointwise graph equations are eliminated extensionally. The audit also found a prior Boolean-slack substitution idea in packet m; that is a scalar certificate branch proof, not these function-valued composition tails. Keep the claim this narrow.

**Validation:** fresh copies of the pinned `Representation` and `ArithmeticRepresentation` dependencies were compiled, followed by both complete replacement modules. `Compatibility.lean` reconstructs the exact old `Rep.compose` and `GraphRep.composeDirect` constructors, and proves each entire old/new representation record equal by `rfl`. This checks the expression syntax, witness counts, and all data fields, not merely equality of represented predicates. Old/new constructor axiom reports are recorded separately and agree. No performance improvement is claimed from these single runs.

## Artifact map and status

- `structural/structural.patch`: exact proposed source hunks for all three modules.
- `structural/candidate/DiophantineConsistency/*.lean`: complete replacement modules, plus the two unchanged pinned dependencies used for compilation.
- `structural/StructuralKernels.lean`: both generic mechanisms and the exact unique-factorization theorem, compiled independently.
- `structural/Compatibility.lean`: complete original constructors and `rfl` comparisons.
- `structural/modules-validation.log`: fresh dependency and full-module build receipts.
- `structural/final-validation.log`: final exact kernel/compatibility axiom receipts.
- `structural/metrics.json`: original/candidate physical lines and SHA-256 values.

Combined measured candidate delta: **20 physical Lean lines removed** across the three source files. Of these, 10 lines are removed in two full-module-compiled edits; the remaining 10 lines are removed by a patch whose exact theorem kernel compiled. This is a modest, tightly verified addition to the assumed-applied earlier proposals.
