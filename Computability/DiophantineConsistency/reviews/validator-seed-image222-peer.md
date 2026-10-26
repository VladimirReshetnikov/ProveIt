# Independent source review: actual internal C222 seed image

Read-only mathematical, source, and provenance review by
`complemented47_review`,2026-10-26. Result: PASS within the stated scope;
no correction requested. I read the complete138-line main,53-line checks,
author receipt, both complete embedded drivers, and replay metadata. I also
read the exact literal seed templates, actual CProv definition/rules, the
complete SeedWitness and SeedClosure sources, and the invoked finite
quantifier/propositional contracts. I did not compile or execute the
received drivers, change frozen sources/objects, or perform Git operations.

## Exact sources

- `ZFCinPA/ValidatorSeedImage222.lean`:
  `96c7b803fa0a11578545c8cabbdab6cd2b1321e21497f82ee895ce9610ecf511`.
- `ZFCinPA/ValidatorSeedImage222Checks.lean`:
  `b96821ce186a0b757994727c85c71e3f3c44bcc2d7c6cdc72318491010a35e72`.
- [Author receipt](validator-seed-image222-author.md):
  `24141981004d6028e80197be390bd4aee9772266da897061e4a2d2f653517328`.
- [Complete replay inventory](validator-seed-image222-replay.json):
  `d79bf3855cd650c5d4df1a80ce4460ad3c513f774038c92efad3ca1a32bec0a7`.

Source root: `Logic/Interpretability/ZFCinPA/Lean`. Relevant frozen bindings
are SeedClosure `e0fa4d18aca886701bfc6a4593f2b468372e4bc220d497cdfe05aa25e1d77d83`,
SeedWitness `fb0b8fc33cc081550caffb46ea819d03b6218034d8afa845bf990affc19eb010`,
RelationalCore `3246a40dae816446a560652ff334ad44026752e176e577328622b236855a47a9`,
Provability `a3b50d8088d288ee951f2a9612e624e54ea78814151aaa3a2acc083242ac78b2`,
and literal ArithmeticSeedTemplates
`d0f878669c9f8c8c9d94bccf451544aba6f7304368355f0bba440999ce342a59`.

## Mathematical findings

All theorem premises are explicit: an arbitrary `ORingStructure V`
satisfying IΣ1. Labels and matrix codes range over that same internal model.
The main construction uses the actual new `CProv`, namely an internal code
whose `ArithmeticHistory222.value` is the formula code plus one. It does
not invoke standard-model truth or old C254 derivability as an oracle.
Old template names for unchanged numeric constructors/rho6 do not change
that actual checker binding.

`closure_support_exists` correctly keeps the existential input binder:
the actual negative universal is converted by `not_all_imp_ex_conj`, then
its left conjunction component is projected under `ex_mono`. No `Vac a p`
is available or used. The result is precisely
`forall b (b in k -> exists a p)`, including coincident labels and code0.

`closure_coverage` projects the other component and applies the exact
`ex_all_elim`/rho6 certificate. Thus the resulting input label `a` is free
inside `subset a b k`; it is not additionally universally generalized.
The local deductions first discharge the membership implication, and only
then use `all_mono b` on a proved implication. No hidden generalization under
an undischarged membership assumption occurs.

`seed_image` retains exactly `c != a` and `c != b`. The actual seed's
self-labelled matrix is still `c`; neither `Vac a c` nor `Vac c c` is added.
The check `seed_image 1 1 0` correctly preserves both legal diagonal roles
and the zero container label.

The request and closure congruences use implication contravariance in the
antecedent, covariance in the consequent, negation reversal, and actual
universal monotonicity at every printed binder. They replace only the
matrix while retaining the same numeric container label. Consequently the
DNI/DNE equivalence between arbitrary `p` and `pad p` can be transported
through both literal circuits and through the fixed outer existential;
there is no capture-avoiding substitution claim or binder renaming hidden
in this step. `pad_gt_three` follows actual Cantor component bounds, so
roles1/3 satisfy both seed gates for every internal p, including p=0.

`matrix_image_witness` is exactly the advertised internal checker witness.
Its Nat check uses the previously proved actual C222 adapter only after the
all-internal theorem is obtained. The result is support, a root request,
and subset-indexed coverage. It does not prove raw-membership CP/GIC,
tagged comprehension, semantic seed validity, arbitrary represented-proof
translation, or an HA proof of the equation equivalence.

## Authentication and limits

A separate read-only hash scan verified all596 distinct recorded files:
128 selected current custom sources,413 object/companion files,38 external
boundaries, compiler/manifest, parent receipt, fresh leaf sources/objects,
logs/timings/snapshots, complete drivers, input inventory and run record.
Every recorded hash matched. All128 current import headers were reparsed
and agree with the inventory. The128 custom modules include95 Foundation
modules. Both embedded driver texts hash to their recorded files.

The author reports two first-attempt exit0 builds under
`-M6000 -j1 -DElab.async=false`; main log is empty, and all14 recorded axiom
reports use only propext, Classical.choice, and Quot.sound. I read these logs
and commands, but did not independently replay them. Their authenticated
prerequisites are reused, not freshly compiled by this review; the explicit
38 external boundaries remain a package boundary rather than a full source
closure claim.

I previously contributed read-only plan challenges to SeedWitness and
SeedClosure and reviewed several arithmetic/C222 prerequisites; I authored
none of this SeedImage implementation. Those prior contributions are not
counted as independent implementation or fresh compilation here.
