# Direct-ordinate 86 HA proof-existence: fresh-parent author extension

`HAAdaptiveDirectOrdinate86.ha_equivalence` is a Lean theorem of type

```text
ProofEquiv (ArithmeticExpression.noZeroSentence naturalExpression86)
           FoundationHAConsistencyNormalization.ordinaryConsistency
```

`ProofEquiv a b` abbreviates HA `Proves ((a → b) ∧ (b → a))`; `ordinaryConsistency` negates the formal provability predicate for contradiction in Foundation's `ZermeloFraenkelChoice` theory. Thus, within the checked Lean development, the theorem establishes existence of an HA derivation of both directions for this exact formalized 86-expression no-zero sentence. It does not print a literal HA proof. The check reports only `[propext, Classical.choice, Quot.sound]` as Lean metatheory axioms, not added axioms of HA.

The author run `/tmp/ha86-focused-extension-uut_8s59` finished `PASS` after compiling 27 exact current-source modules directly, without a compatibility shim, on `/tmp/ha87-focused-validator-rebase-3tvgyxbr`. That 87 parent is the fresh peer that compiled all 83 of its modules against one overlay, with no reused rows; its state SHA-256 is `87495220e1dc982922a8fce7e533640892693a81cf67612b64b29630e6d1ff97`. The extension reauthenticated 730 distinct parent source guards, 1,322 selected project objects, all 83 parent output/full-log records, its source snapshots, and provider/graph/plan/package anchors before and after. The focused parent still inherits historical HA/ZF/Foundation/Mathlib/package ancestry and unlisted boundaries; this is not a complete source-current closure claim. A separate independent build of this 86 extension is required before acceptance.

Reproduce with `HA86_PARENT=/tmp/ha87-focused-validator-rebase-3tvgyxbr python3 Computability/DiophantineConsistency/research/wang-chunk-full/build_ha_direct_ordinate86_peer.py`. State SHA-256 `7712aa0d4c2e7cd8497dd387147dd382bfe32db4616fe2014273d712492b01e8`. Endpoint source SHA-256 `c162b434e82681491e565e078ee38a4c72820c6914a865ead11bd4f87628a3be`, object `6af265a51e343b1e8e988f499f10d8160481372500ba2b652d0caed3a6ea9a69`, empty full log `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. The check source is `8e8ca7c4632ee4ccd76f3c0147876f31dbe3d229bed07f832c74c6e3377ac67e`, object `d711c0e35bc9e4eb62e5947f74393cecdc082c708111800ec0343ee82550a9b7`, and full log `e9bdcac679e8f38b22fef13da4068a55b5e5b6e243b87c5aea7210e7643e77a4`. The only other nonempty log is the previously documented auxiliary-norm-client unused-simp warning. All 27 object and full-log hashes also match the earlier extension built on the now-qualified reused author parent; matching these outputs does not retroactively authenticate that earlier parent.

The deterministic literal generator was separately run as described in `ha86-focused-extension-author.md`: its output SHA-256 `449650adad654ff14ed7653f04187d7aad4696b2e5fc0b8262a7d96897ebfad5` matches the compiled literal source, and the pinned candidate JSON SHA-256 is `e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f`. This is a separate generator check, not part of this driver's pre/post guards; the 86 count is an unshifted graph operation count, not a minimality certificate.

State, driver, 1,322-object inventory, all 27 source snapshots, full logs and timings are in `ha86-fresh-parent-extension-author-evidence`; `FILES.json` SHA-256 `20a167157a7deaab469fcb4b1b91c8faaead6891d7a21e0f040b615d9aec78d7`.
