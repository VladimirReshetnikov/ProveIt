# Normalizing universally closed induction axioms before cut elimination

`ParsonsClosure.paired_closure` gives an LK derivation of
`∀parameters P ⋎ ∃parameters Q` from any LK derivation of `P ⋎ Q`, using the
same finite parameter block on both sides. Applying it to the existing open
induction normalization yields `closed_induction_normalization`, a derivation
of the actual universally closed induction axiom disjoined with the
parameter-closed existential counterexample matrix. It retains the explicit
finite parameter block rather than assuming a pairing function.

`normalize_closed_list` applies that derivation to replace each negative
universally closed induction axiom in an arbitrary finite list, retaining the
other context and handling repeated axioms. It may introduce cuts.
`normalized_cut_free` then invokes Foundation's cut-elimination theorem and
returns a cut-free derivation of exactly the normalized sequent. This is a
closed proof transformer for this preprocessing stage; the caller supplies
the finite list and the initial sequent derivation.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match; all
8 printed axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`. The [16-file replay manifest](parsons-closure-replay/FILES.json)
has SHA-256 `f5c6a019ab2ae7d182d0455367d397ccc9fb31f27463d6ce6f956eb3b477168f`.
Direct prerequisites were previously built `ParsonsInductionCase`,
`ParsonsRule`, `ParsonsGuard`, and `ParsonsSelection`; Foundation/Mathlib
objects are an inherited boundary, not a fresh transitive source audit.
Scratch attempts around the existential closure identity failed before being
fixed; their console logs were not retained.

This preprocessing result does not translate the resulting cut-free proof
into the induction-rule calculus or eliminate the induction axioms. The
existential-block logical cases, strict Π₂ side-form adapter, and the
rule-to-PRA witnessing theorem remain open. No overall conservation result
or PRA proof of the target is claimed.

A third independent replay at `/tmp/parsons-closure-build-c8yjj22q` matched
both source and object hashes and full logs of the author builds. All 16
author-manifest entries matched. The direct providers match the previously
reviewed induction-case overlay. The [independent replay](parsons-closure-independent-replay/)
has the same inherited Foundation/Mathlib boundary.
