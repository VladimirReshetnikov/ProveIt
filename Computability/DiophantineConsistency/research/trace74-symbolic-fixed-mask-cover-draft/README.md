# Structural symbolic fixed-mask cover draft

This uncompiled source proposes the actual symbolic natural inequality `betaNat+1 <= lowNat+highNat` and its cast to every IΣ₁ model. It uses no `decide` over the full 590,069-bit constants: the low mask's defect has no nonzero digit beyond index 3296, so a 3297-digit `Nat.ofDigits` bound makes the defect less than `B^3297`, where `B=2^67`; the high mask has a positive `mu` digit at index 4393, so it is at least `B^4393`. The existing `digits_add_defect` identity and beta definition would then yield the cover.

The proposed support truncation, high-list split, exact Lean lemma names and elaboration/resource behavior remain unchecked. This is a natural/model mask inequality draft only; it does not prove a no-carry condition from a 74 zero, the fixed-BFS guard or a graph equivalence. No Lean run has occurred.

The [independent source review](../../reviews/trace74-symbolic-fixed-mask-cover-draft-independent/README.md) checked the support and high-digit positions, radix identities and inequality direction. It did not run Lean or establish selected-provider compatibility.
