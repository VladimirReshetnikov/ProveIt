`DuplicateProfiles.lean` proves that equality-free `ModelsCPGIC` and raw
irreflexivity do not supply `Code254Models.ModelsDecoded` on the same raw
structure. The result is conditional on an explicitly supplied starting
model and domain witness. It asserts neither existence nor inconsistency
of that model class, and it does not refute an equiconsistency proof that
constructs a different model.

The distinction is present in the actual interfaces. `ProfileModel.ModelsGIC`
ranges over equality-free `Form` matrices. The numerical decoder also
produces native equality atoms, and `Code254.bundle` includes GIC for those
matrices. Its atomic equality-vacuity row is harmless under the existing
freshness gates; the equality-bearing GIC matrix is the additional obligation.

The construction duplicates every object, using domain `V × Bool` and

```text
duplicateMem (x,i) (y,j) := mem x y.
```

`sat_duplicate` proves the satisfaction projection for every actual
equality-free formula, including quantifiers and arbitrary parameter
valuations. `models_duplicate` applies it to the literal container formula
and each equality-free GIC formula. Irreflexivity transfers separately.
No schema for arbitrary external relations is assumed.

Every represented set in the duplicate contains either both tagged copies
of an object or neither. Consequently no object has a literal native
singleton. But one native-equality GIC matrix already demands such a
singleton: `gicForm (fEq 1 2)` with its parameter equal to p collects outputs
equal to p. CP supplies a domain set containing p. The coverage clause
puts p into the image, and the global-support clause makes every image
member equal to p. `duplicate_not_point_gic` proves failure of this actual
first-order instance without using irreflexivity.

The same obstruction occurs in an actual numerical bundle. The checked
identity is `Code254.enc (NF.eq 1 2) = 35`. With input name0, output name1,
and the fresh matrix/binder code35, the literal `namedG` tree requires a
singleton of the object held at name2 whenever name1 holds a nonempty
domain set. `singletonCarrier_mem` checks that the whole corresponding
named bundle is an actual `EncBundle` axiom with both gates satisfied.
Irreflexivity supplies the relative-falsity semantics; the existing
decoded-to-encodable adapter then yields `duplicate_not_decoded`.
`duplicate_obstruction` packages all three statements about the same
duplicate relation: actual equality-free CP/GIC, irreflexivity, and failure
of the decoded numerical model obligation.

This isolates a possible next resource rather than forcing raw incoming
Extensionality. Mathematically, actual singleton existence implies
outgoing-profile faithfulness,

```text
(∀z, x∈z ↔ y∈z) → x=y.
```

Conversely that finite resource lets an equality-free outgoing-profile
formula represent native equality. A separate hygienic formula translation
could then extend equality-free GIC to native-equality GIC. Ordinary Pairing
in an actual equality-bearing model already supplies the singleton resource.
These are recommendations for the reverse adapter; the current module
proves the obstruction and does not implement that translation or assume
ZF0 implies GIC.

Pinned absolute Lean 4.32.0 checked the source in 0.407 seconds, followed by
fifteen theorem axiom audits and three caller examples in 0.288 seconds.
All audited axioms are among `propext`, `Classical.choice`, and `Quot.sound`;
three audited lemmas are axiom-free. There are no admissions, custom axioms,
or `native_decide` calls. The callers refute an asserted uniform reverse
adapter, exhibit the failed actual equality GIC instance, and demonstrate
why the satisfaction projection cannot extend to native equality.

The scoped check reused the verified parent cache through
`/tmp/zfc-decode-fresh254-_v5vy411`; no full closure or bootstrap was rebuilt.
Development logs retain explicit environment-projection, Boolean-tag, and
definitional-unfolding fixes. Final source and audit output have no warnings.
Commands, hashes, caller source and complete axiom output are retained in
`results/duplicate-profiles-verification.json` and
`/tmp/zfc-duplicate-profiles-ky69nyzd`.
