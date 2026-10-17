The literal permutation machine has **252 working states and 504 total
transition rows**. `BinaryPerm252.lean` now proves that its actual standard
blank-tape run halts exactly when the original numeric calculus C254 has a
refutation. Equivalently, it halts exactly when `Code254Proof.check` accepts
some natural-number proof of falsity, when the exact native theory has a
refutation, or when the repository's full ZF theory `ZFax_s` has a refutation.
The negated statements give the corresponding nonhalting equivalences.
The subsequent [Choice calibration](choice_calibration254.md) extends this
closed endpoint to **nonhalting iff Con(ZFC)** for the same literal table.

These final statements have no coverage, register-operation or chosen-start
premise. They compose the closed certificate for all 233 literal decoder
chunks and 8,391 guard cases, the exact 82,552-transition blank bootstrap,
the complete-tape positive-segment runtime simulation, and the safe
zero-register program endpoint. Spares remain part of the tape relation.
The finite bootstrap endpoint is not asserted to be its first arrival.

The frozen canonical table has SHA256
`8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797`;
the old-label table has SHA256
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
Attribution remains Mira-Cult's original machine and calculus, Jeff's
verification at `297ab8df7e5de329605c3875b4934643b371a5e3`, Wade's compiler
framework, and mira-emmy's public253 reduction at PR20 head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. The new register permutation
and its blank initializer use the same charged working-state table.

The final source passed a fresh explicitly pinned Lean 4.32.0 check in
0.529 seconds. Its thirteen axiom reports and ten endpoint/count caller
checks passed; the callers took 0.453 seconds. The reported axiom set is
only `propext`, `Classical.choice` and `Quot.sound`. Previously checked,
source-matched dependencies were reused rather than recompiling the full
closure. Exact commands, versions, hashes, caller source and outputs are in
[the verification record](results/binary-perm252-verification.json).
An initial scratch import-layout failure is separately retained there;
correcting the dependency overlay required no proof-source change.

`ZFCBoundPerm252.lean` adds the standard-theory implications: a ZF0 refutation
makes this blank machine halt, and Con(ZFC) implies its nonhalting. The latter
uses the exact ZF endpoint and inclusion of ZF axioms into ZFC. The
[153-unit integration](results/binary-perm252-integration-verification.json)
freshly checks this module, the umbrella and six joint callers; all151 reused
source identities match their successful scoped checks. The complete9Sites
objects and the Binary object also match the recorded checked artifacts.
This integration does not rebuild all153 modules.

`ChoiceCalibration254.nonhalting_iff_zfc_consistency` now supplies the full
external Lean equivalence with standard ZFC consistency. It combines this
binary/ZF endpoint with Choice in the constructible subtype and a refutation
comparison through external completeness. The
[165-unit integration](results/choice-calibration254-integration-verification.json)
checked that final composition. The later
[167-unit integration](results/binary-zfc252-integration-verification.json)
also checks `BinaryZFC252` from the independently supplied Choice bridge
against the actual binary objects, and refreshes every affected consumer.
Both final statements have no additional premise.

The PA formalization remains open: the accepted natural-number proof witness
exposes an interface for arithmetic work, while represented proof and finite
trace translations still need completion. The result establishes neither
unconditional nonhalting nor minimality.
