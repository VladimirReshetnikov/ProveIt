# Universal induction parameters

`ParsonsParameters` deals with the actual universally closed axiom used by
Foundation, with any finite number of parameters. `neg_closed_ind` identifies
its negation exactly with a finite existential block over `parameterBody`.
After substituting an arbitrary vector of terms, `parameterBody_instance`
recovers the negation of `succInd` applied to the corresponding term-rewritten
formula. `parameter_instance_sigma` certifies that this rewritten formula
remains Σ₁, and `instance_normalization` supplies the existing explicit LK
normalization into the existential counterexample matrix for that opened
instance. There is no pairing assumption, and the terms may have arbitrary
free parameters.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both object files and complete logs match;
seven printed axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`. The [16-file replay manifest](parsons-parameters-replay/FILES.json)
has SHA-256 `f54ad34749a2e0d9c335a050dfa76217794b6f29c2322a1ed87fd27b76e25e6c`.
Direct prerequisites were previously built `ParsonsInductionCase`,
`ParsonsRule`, `ParsonsGuard`, and `ParsonsSelection`; Foundation/Mathlib
objects remain an inherited boundary and were not independently re-audited.
Initial scratch attempts had parser and rewrite-equality failures; the console
logs were not retained.

This identifies the parameter block and what its fully opened body means; it
does **not** yet supply the induction on the existential block in a cut-free
proof. The opened-instance normalization is an LK derivation and may require
cut when inserted into an existing derivation, so it cannot be substituted
into the height-decreasing recursion without an additional argument. Strict
Π₂ side-form normalization, remaining logical cases, and rule-to-PRA
witnessing also remain open; this is not a conservation theorem.

A third independent replay at `/tmp/parsons-parameters-build-01_pqfz5`
matched both source and object hashes and full logs from the author builds.
The direct induction-case object matches the previously accepted independent
replay; the other direct provider hashes were checked at that checkpoint.
All 16 author-manifest entries matched after resolving their relative paths
against the manifest directory. The [independent replay](parsons-parameters-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
