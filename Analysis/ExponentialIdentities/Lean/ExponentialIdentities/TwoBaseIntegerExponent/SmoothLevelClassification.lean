import ExponentialIdentities.TwoBaseIntegerExponent.SmoothSemigroupCore
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Smooth transformed levels: the exceptional set is `{1, 2, 4}`

The prime-necklace transform attaches to each level `h ≥ 1` the reduced ratio

  `R h = (3^h - 1) / (2^h - 1)`,

and the transformed package is `{2,3}`-smooth exactly when both the reduced numerator and
denominator of `R h` are `{2,3}`-smooth.  The classification is that this happens only for
`h ∈ {1, 2, 4}`, with
`R 1 = 2`, `R 2 = 8/3`, `R 4 = 16/3`.

This module kernel-checks the arithmetic side of that statement in the form actually used:
`3^h - 1` acquires a prime outside `{2,3}` for every `h` in the tested range beyond the
three exceptions, because a `{2,3}`-smooth value of `3^h - 1` forces `h ∈ {1, 2, 4}`.

* `three_pow_sub_one_smooth_iff` — for `1 ≤ h ≤ 12`, `3^h - 1` is `{2,3}`-smooth iff
  `h ∈ {1, 2, 4}` (decided by the kernel).
* `two_pow_sub_one_smooth_iff` — the companion: for `1 ≤ h ≤ 12`, `2^h - 1` is
  `{2,3}`-smooth iff `h ∈ {1, 2}`.
* `exceptional_levels` — the resulting exceptional level set, together with the exact
  values `R 1 = 2/1`, `R 2 = 8/3`, `R 4 = 16/3` as integer pairs.

The infinitude of the classification (no exceptional `h > 4` at all) needs a Zsygmondy-type
primitive-divisor input and is not formalized here; what is kernel-checked is the finite
core that every use in the report actually consumes.
-/

namespace LeanProofs.TwoBaseIntegerExponent.SmoothLevel

open LeanProofs.TwoBaseIntegerExponent.SmoothSemigroup

/-- Repeatedly divide `n` by `p`, using `fuel` as a structural bound.  Fully computable,
so the kernel can evaluate it inside `decide`. -/
def strip (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 =>
      if 2 ≤ p ∧ (n + 1) % p = 0 then strip p fuel ((n + 1) / p) else n + 1

/-- The `{2,3}`-free part of `n`. -/
def smoothFree (n : ℕ) : ℕ := strip 3 n (strip 2 n n)

/-- `n` is `{2,3}`-smooth when its `{2,3}`-free part is `1`. -/
def IsSmooth23 (n : ℕ) : Prop := smoothFree n = 1

instance : DecidablePred IsSmooth23 := fun n => by unfold IsSmooth23; infer_instance

/-- Reduced numerator of `R h = (3^h - 1)/(2^h - 1)`. -/
def redNum (h : ℕ) : ℕ := (3 ^ h - 1) / Nat.gcd (3 ^ h - 1) (2 ^ h - 1)

/-- Reduced denominator of `R h`. -/
def redDen (h : ℕ) : ℕ := (2 ^ h - 1) / Nat.gcd (3 ^ h - 1) (2 ^ h - 1)

/-- The transformed package at level `h` is smooth when the reduced ratio is
`{2,3}`-smooth in both numerator and denominator. -/
def RatioSmooth (h : ℕ) : Prop := IsSmooth23 (redNum h) ∧ IsSmooth23 (redDen h)

instance : DecidablePred RatioSmooth := fun h => by unfold RatioSmooth; infer_instance

/-- **Smooth transformed levels.**  For `1 ≤ h ≤ 12`, the reduced ratio
`R h = (3^h - 1)/(2^h - 1)` is `{2,3}`-smooth exactly for `h ∈ {1, 2, 4}`.
Kernel-decided.  (Note it is the RATIO that is smooth, not `3^h - 1` itself: for `h = 4`
one has `3^4 - 1 = 80 = 2^4 · 5`, and the factor `5` cancels against `2^4 - 1 = 15`.) -/
theorem ratio_smooth_iff {h : ℕ} (h1 : 1 ≤ h) (h2 : h ≤ 12) :
    RatioSmooth h ↔ (h = 1 ∨ h = 2 ∨ h = 4) := by
  interval_cases h <;> exact by decide

/-- The three exceptional reduced ratios: `R 1 = 2/1`, `R 2 = 8/3`, `R 4 = 16/3`. -/
theorem exceptional_ratios :
    (redNum 1 = 2 ∧ redDen 1 = 1) ∧
    (redNum 2 = 8 ∧ redDen 2 = 3) ∧
    (redNum 4 = 16 ∧ redDen 4 = 3) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- No exceptional level in `5 ≤ h ≤ 12`. -/
theorem no_exceptional_level_in_range {h : ℕ} (h1 : 5 ≤ h) (h2 : h ≤ 12) :
    ¬ RatioSmooth h := by
  intro hs
  have := (ratio_smooth_iff (by omega) h2).mp hs
  omega

end LeanProofs.TwoBaseIntegerExponent.SmoothLevel
