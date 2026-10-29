# Side formulas in the principal induction case

`ParsonsSide.side_complexities` certifies that all three side-disjunctions
used by `ParsonsInductionCase.one_case` are Π₂ in Foundation's hierarchy when
the induction formula and the side formula are Σ₁. The other two lemmas
isolate the Σ₁ base and Π₂ step calculations. These are classifications in
the hierarchy that allows non-prenex formulas; they do not construct the
strict `∀x ∃y` normal form, its proof equivalence, or its witness encoding.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match; the
three printed axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`. The [16-file replay manifest](parsons-side-replay/FILES.json)
has SHA-256 `e26e93a2a8c383937c8ff522f1ddf867999245df3d4a1b092296d4c21a195c97`.
Direct prerequisites were previously built `ParsonsRule`, `ParsonsGuard`,
and `ParsonsSelection`; Foundation/Mathlib objects are an inherited boundary,
not an independent transitive source audit. The first scratch attempt failed
on type inference and a simplified hierarchy goal; its output was not retained.

The strict Π₂ normal-form adapter and its translation in a finite sequent
remain open, as do the full induction-axiom reduction and PRA witnessing.

A third independent replay at `/tmp/parsons-side-build-_cz31zod` matched
both source and object hashes and full logs of the author builds. All 16
author-manifest entries matched. The direct providers match the previously
reviewed induction-case overlay. The [independent replay](parsons-side-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
