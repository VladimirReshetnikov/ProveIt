# Source review of the conditional standard and reference iPRA adapter

I reviewed the three theorem statements and their immediate source-level
interfaces in `PositiveModelIPRAStandardAdapter.lean`, SHA-256
`7046c2d8fde9411d517641829e3158733bfec14e778fdce6cb7d86cc9f3ccb78`.
I found no mismatch in their hypotheses, formula directions, selected
consistency predicates, or application of order erasure. This is a source
and receipt inspection, **not a fresh Lean replay** or an audit of the full
underlying proof chain.

All three theorems quantify over an arbitrary finite expression `e` and
require the explicit `PositiveModelBridge e`: in every IΣ₁ model a positive
zero of that same `e` exists iff the specified machine internally halts.
The checked native adapter obtains its no-zero formula for the adaptive
`positiveShift e`, which substitutes `x+1`. Thus the standard theorems do
not establish an endpoint for a concrete expression without that bridge.
`nativeNoZero` is the universal closure of the negated equality between the
two natural expressions from `splitNatural`.

`standard_equivalence_of_positive` applies the native-to-standard direction
of `IPRAStandardTheory.provable_iff` to the native theorem. The right side is
exactly `∼mappedNativeRefutation embedding`, where the mapped predicate is
the native reading of the language-mapped Foundation refutation sentence
`rho`. `rho` is `provabilityPred` for Zermelo–Fraenkel set theory with choice
and falsity, and the selected Foundation `sourceSentence` is definitionally
`∼rho`; these are formal syntax, not an assertion of either consistency or
inconsistency. The selected [source definition](../../Lean/DiophantineConsistency/FoundationHAConsistencyNormalization.lean)
has SHA-256 `1a69a875738db6ebbd7c5e466022d0d169ee747e50184fc838077d42f0ad8e09`.

`standard_translated_of_positive` composes the no-zero/refutation-negation
iff with `IPRABoundedRhoZFC.zfcEquiv`, whose displayed direction is the
Gödel–Gentzen image of the **mapped** source sentence iff the same refutation
negation. The first implication uses the left side of the native iff followed
by the right side of `zfcEquiv`; the converse uses the other two sides in the
reverse order. Its conclusion is precisely
`(Semiformula.lMap embedding sourceSentence)ᴺ`: mapping precedes translation.
It is not an unproved general transfer of arbitrary IΣ₁ theorems to iPRA.

`reference_equivalence_of_positive` applies the existing one-way
`nativeToReference` transfer to the native iff. `erase` recursively
preserves propositional structure and turns `<` into equality with the
comparison-code output `1`; its equality case retains equality. Thus the
result is the erased no-zero formula iff the negation of erased mapped
refutation, in `referenceTheory`. This theorem does not assert the converse
theory transfer or separately prove a reference-theory translated-consistency
client. The referenced source hashes are pinned by `check.py`.

The independent point-in-time `python3 -I -S -B check.py` check exited 0 in
`observations/attempt02`. It checked 19 pinned files, including the adapter
source and run copy, both author receipts, the direct native adapter source
and object, and the workspace sources used for this interface reading. The
standard author receipt hash is
`8f1f5cd6bb92885dbab9bb9d8eb29fa350be78da3a848abedcd95e212b38720e`;
the native receipt hash is
`9b401cd44c874ad80fe2d4415195b7e2adb228f0f2a291af7afdb66bbbf1944b`.
The standard author object matches its reported hash
`1fb7efa7fe6adce191c37dd9fc457ca4af4dd02210b3a19e6ae110d46fea9ce5`;
its direct dependency/companion guards and all 1,497 recorded selected
provider file records still match at this check. The author logs report
`[propext, Classical.choice, Quot.sound]` for the three theorems; these are
Lean metatheory dependencies, not stated object-theory axioms. The check
source hash is `8355b501c717ebaea76fd6a7671ca186192b6b45563a0d680f7dc4ad650e6ce9`
and its successful output hash is
`44cf4fa37e20d790a2548e25733594b59ad81a91ba8506117ee1b8097cddef55`.
Attempt01 was also successful; attempt02 additionally verifies the native
source receipt and recorded provider-unchanged flag.

The live workspace source readings do not by themselves certify that every
historical provider object was built from those exact source files. Neither
the retained receipt nor this inspection checks complete project/package or
dynamic ancestry, continuous filesystem immutability, the compact model
bridge, a coherent compact/provider join, the retained bytes, or a PDF.
