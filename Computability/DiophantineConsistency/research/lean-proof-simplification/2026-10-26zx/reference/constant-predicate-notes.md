# Optional proof-only simplification: constant input sets

## Target and mechanism

`Computability/DiophantineConsistency/Lean/DiophantineConsistency/Computability.lean:291`
defines `refutationInputs : Set ℕ := fun _ => C222 F`. Hence this is a constant
predicate, and every fixed constant predicate is classically `ComputablePred`.
The two possible programs always return true and always return false; classical
logic proves that one is correct without effectively selecting it from the
proposition. `ComputablePred.to_re` proves the existing r.e. proposition directly.

The intended local substitution at lines 294–307 is:

```lean
theorem refutationInputs_re : REPred refutationInputs := by
  classical
  exact (Computable.const (decide (C222 F))).computablePred.to_re
```

The repository declaration itself has not been recompiled here; the standalone
`ConstantPredicate.lean` checks the mathematical/API core against Lean 4.32.0 and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`, with exit code 0. The log
records the runtime and all dependency commit IDs. There are no `sorry` terms.
The pure selector-invariance theorem uses no axioms; the computability theorem
uses only the reported standard axioms `propext`, `Classical.choice`, and
`Quot.sound`. This is core validation, not a full project rebuild.

## Scope and tradeoff

This replaces only the r.e. proof body. It must not be presented as removing the
private primitive-recursion development: `haltingTest_natPrimrec` at line 314
still uses `pr_boundedRun`, and the explicit bounded test and actual direct
program certificates remain valuable and necessary. There is no claimed speedup,
coefficient recipe, or effective decision procedure for syntactic consistency.
The original docstring says “by the actual verified enumerator”; that provenance
claim must be changed if the proof is replaced. An alternative is to keep the
existing theorem as the explicit provenance endpoint and use the shortcut only
in an existence-oriented module, but that does not reduce total source by itself.

The direct replacement is 11 theorem lines shorter (14 lines to 3) before any prior
baseline adjustments. The review patch saves 10 total lines because its corrected
docstring adds one line. A generic helper is optional and must be charged to net
savings; do not inflate the local saving into removal of a whole module.

## Why downstream noncomputable polynomials are preserved

`Polynomial.lean:61` defines `ninePolynomial A hA` with
`Classical.choose (Jones1982.nine_unknowns hA)`; lines 77–84 similarly define
`quarticRepresentation` and `quarticPolynomial`. Its file header explicitly says
these choices do not provide an executable coefficient recipe. The parameter
`hA : REPred (fun _ : ℕ => A)` is a proof in `Prop`. Replacing it by another proof
of exactly the same proposition leaves the selected values definitionally equal,
by Lean proof irrelevance. The certificate proves the generic selector and
`Classical.choose` invariants with `rfl`.

This argument requires identical predicates/specifications and changes to proof
arguments only. It does not justify replacing the Jones specification, changing
the polynomial definition to `if A then 0 else 1`, or substituting different
explicit `ScalarPR`/machine data. It does not make classical choice executable.

## Recommendation

Treat this as an optional, small simplification for the extensional existence
branch. If actual-enumerator provenance is a requirement on `refutationInputs_re`
itself, retain the current proof and record this as an interface observation,
not a recommended replacement. The mathematically honest advantage is a shorter
proof of the stated proposition; the explicit algorithmic story remains a
separate requirement that this proof does not fulfill.

Novelty status: independent strict corpus audit cleared this optional idea,
including text notes and the zp/zq reports. No analogous fixed-proposition,
classical-constant-predicate, or non-effective-polynomial mechanism was found;
mentions of `refutationInputs_re` were inventories. This is a corpus result,
not a claim of novelty in computability theory.

`constant_predicate_proposal.patch` is a reviewable, unapplied source diff.
It includes the necessary provenance-documentation correction. The generic
proof core is Lean-checked; the production-module diff was not compiled.
