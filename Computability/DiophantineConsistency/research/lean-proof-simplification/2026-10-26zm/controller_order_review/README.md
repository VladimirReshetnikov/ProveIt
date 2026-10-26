# Zero-index exact-order reuse (small candidate)

Frozen source pin: `e1c8914bc7064d9a8e7c06171a18069a949badd0`.

The two identities at the first prime-power level are not separate arithmetic obligations once their exact-order families have been proved:

- `CurrentAuxiliaryOrder2011.generator_order_succ 0` states that the generator has order `auxiliary^0 = 1` modulo `auxiliary^(0+1) = auxiliary`. Thus `generator_cast_auxiliary` follows from the already-used `orderOf_eq_one_iff.mp`.
- `CurrentPowerCoordinates2011.full_order 0` similarly has order one modulo `d * auxiliary`. It proves `generator_cast_C0` directly, without a second CRT-order computation.

The replacement changes only these two proof bodies. The complete file goes from **105 to 102 lines**, with no new helper or import, and no public statement or executable definition changes. This is a modest maintenance simplification, not a new controller theorem or an asymptotic/kernel-speed claim.

## Files

- `CurrentPowerCoordinates2011.lean`: complete replacement file.
- `order_zero_specializations.patch`: exact patch against the frozen source.
- `metadata.json`: hashes and complete-file line counts.
- `verify.py`, `validation.json`: reproducible source replay / arithmetic crosschecks and original validation receipt.

## Source-level check

`generator_order_succ` is already imported via `CurrentAuxiliaryOrder2011`; its proof depends on the checked principal-unit facts, not on `CurrentPowerCoordinates2011`. `full_order` is declared before `generator_cast_C0`, and uses `generator_cast_fixed` plus `generator_order_succ`; it does not depend on `generator_cast_auxiliary`. There is no circular dependency.

Both proof bodies use `apply orderOf_eq_one_iff.mp`, which is already present in the same pinned module. `simp only [Nat.zero_add, pow_one, pow_zero]` reduces the modulus and claimed order of the respective zero-index theorem to the precise goal. No assumption is dropped or introduced. The separate `generator_cast_auxiliary` public theorem is retained even though the new `generator_cast_C0` no longer uses it.

The original and candidate public theorem headers and imports are byte-for-byte equal. Patch replay reproduces the complete candidate. Python modular exponentiation confirms the generator equals one modulo 47, 2011, auxiliary, and d*auxiliary, while retaining the nontrivial checked auxiliary-square lift. These are independent arithmetic crosschecks, not proofs that Lean elaborates the patch.

**Lean and Lake are unavailable and were not installed. The candidate is not Lean-compiled.** The exact library declaration text for `orderOf_eq_one_iff` was not locally available; its precise `.mp` interface is anchored by its existing use in the same pinned file.

## Other controller files screened

- `ControllerIntervalSums`: interval injection, card, sum, and explicit starting coordinate already use direct Mathlib finite-sum and unit APIs. No defensible larger reduction found.
- `ControllerOrbitTransport`: affine sum transport and scaled-coordinate quotient are already short; further ZMod/Fin coercion packaging would overlap the assumed baseline.
- `ControllerResidueLift`: quotient-coordinate construction and Boolean/cardinality assembly are mathematically necessary; simplifying casts alone overlaps baseline normal forms.
- `ControllerPowerCoordinates`: injectivity comes from exact order, then finite self-map surjectivity produces the equivalence. Replacing `choose` by an explicit quotient introduces comparable proof plumbing and does not remove all classical choice because `Equiv.ofBijective` remains.
- `PrimePowerOrder`: LTE supplies exact, not merely lower, valuation; the order-one base and prime-power successor cases use different hypotheses. A cosmetic merger is not a new simplification.
- `CurrentAuxiliaryOrder2011`: the checked nontrivial prime-square lift is needed to establish the principal-unit hypothesis; no redundant descending or orbit enumeration proof exists here.

## Proof-dependency tradeoff

The shorter endpoints now rely on the established exact-order family, whose proof traverses the principal-unit/LTE layer. The original endpoint proofs used lighter residue/CRT calculations. File imports and executable data are unchanged, but the per-theorem axiom footprint and elaboration cost have not been measured and are **not** claimed unchanged. This is therefore a small maintenance option, not a performance or dependency-minimization recommendation.
