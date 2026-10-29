# Opening the normalized induction parameter block

`ParsonsOpened.normalized_shape` identifies the exact existential parameter
block produced by `ParsonsTheoryNormalize`. `normalized_instance` proves that
simultaneously substituting an arbitrary vector of terms into its body yields
exactly the existential counterexample matrix for the correspondingly
rewritten induction formula. `counterexample_support` justifies the block
length: the matrix introduces no free parameters outside those of the
original induction axiom. The proof preserves arbitrary free parameters in
the substituted terms and does not assume a pairing function.

`selected_principal` accepts a formula certified by an actual normalized IΣ₁
proof and applies the existing principal counter-witness case after the block
has been opened. The three genuinely smaller local cases are explicit
hypotheses. The separately supplied local derivation is not asserted to be a
descendant of the normalized proof; identifying the appropriate descendant
and furnishing its recursive hypotheses are still part of the full translation.
No height comparison across the earlier cut-elimination operation is claimed.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match; six
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The [16-file replay manifest](parsons-opened-replay/FILES.json) has SHA-256
`125dd0c488d5695e3aead1870b120522f12cef601932a34ae4ff544a73299d23`.
Direct prerequisites were previously built `ParsonsTheoryNormalize`,
`ParsonsClosure`, `ParsonsParameters`, `ParsonsInductionCase`, `ParsonsRule`,
`ParsonsGuard`, and `ParsonsSelection`. Foundation/Mathlib objects are an
inherited boundary rather than an independent transitive source audit.
Scratch attempts around substitution and rewriting equalities failed before
being fixed; their console logs were not retained.

The cut-free logical cases, recursive handling of partially opened parameter
blocks, strict Π₂ side normalization, and PRA witnessing remain open. This is
not an overall conservation theorem.

A third independent replay at `/tmp/parsons-opened-build-yfs984gs` matched
both source and object hashes and full logs of the author builds. All 16
author-manifest entries matched. The direct closure, parameters and theory
normalization providers match their independently replayed objects; the
remaining direct providers match the previously reviewed induction-case
overlay. The [independent replay](parsons-opened-independent-replay/) has
the same inherited Foundation/Mathlib boundary.
