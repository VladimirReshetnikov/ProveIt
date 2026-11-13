# Ring-variable Bd cast-one retry

This source-only candidate preserves the [prior statement and definitions](../nine-seed38-jones-vars-bd-retry01-draft/README.md), replacing the reported unused `Nat.cast_ofNat` simplifier argument with `Int.cast_one` to address the residual integer-cast ones. Rank and sums stay opaque. The guarded check passed Lean compilation and its independent terminal audit. this remains one cut binding, not named-evaluator equality or JSON/document binding.
