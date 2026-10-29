# Principal existential case for Σ₁ induction reduction

`ParsonsInductionCase` formalizes one principal case of Joosten's cut-free
reduction. For an arbitrary open induction formula φ, `matrix φ` is the
one-variable counterexample matrix `base φ ⋏ (step φ ⋏ ¬φ(x))`; its other
free parameters remain free. `matrix_subst` and `matrix_free` establish the
exact substitution and eigenvariable shifts. `induction_normalization` is
an actual Foundation LK derivation of the implication from the negated
**open** `succInd φ` axiom to `∃x, matrix φ`. The context client applies this
using a logical cut and therefore makes no claim to preserve height or
cut-freeness; normalization must precede cut elimination.

For the principal existential introduction, `invert_exists` proves that
all three corresponding matrix premises have cut-free derivations strictly
shorter than the original existential conclusion. `one_case` applies three
explicit **local**, height-bounded recursive hypotheses to those derivations
and uses the actual guarded Σ₁-rule transformer to obtain a rule-calculus
proof of the Σ₁ side formula E. No global conservation premise is assumed.
The local hypotheses still need to be furnished by an induction on the whole
cut-free derivation and its admissible sequent shape.

Two fresh Lean 4.32 builds of main and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match; six
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-induction-case-replay/FILES.json) has SHA-256
`24c63840cc5f63a9b8ea8d9b6b88009313e3d1c30d4fa487f2524424c952a405`.
Direct prerequisites are previously built `ParsonsRule`, `ParsonsGuard`, and
`ParsonsSelection`; Foundation/Mathlib objects are an inherited boundary, not
a fresh transitive source audit. Exploratory scratch failures around cast
transport and the existential normalization were fixed before the final source;
their console logs were not saved.

The universal closure of arbitrary parameters in Foundation's actual induction
scheme, the strict Π₂ side-form normalization, other logical cases, and the
rule-to-PRA witnessing theorem remain open. This is a precise principal case,
not an IΣ₁-to-PRA conservation theorem or a PRA proof of the target.

A third independent root replay at `/tmp/parsons-induction-case-build-tso4mvsq`
matched both source and object hashes and full logs of the author builds.
The three direct provider object hashes matched the previously accepted
`ParsonsRule`, `ParsonsGuard`, and `ParsonsSelection` replays, whose source
hashes also match the current checkout. All 16 author-manifest entries were
verified. The [independent replay](parsons-induction-case-independent-replay/)
has the same inherited Foundation/Mathlib cache boundary.
