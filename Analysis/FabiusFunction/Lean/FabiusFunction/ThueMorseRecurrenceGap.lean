import FabiusFunction.ThueMorseRecurrence

/-!
# Uniform recurrence of Thue–Morse with a linear gap

`ThueMorseRecurrence.thueMorseBit_uniformly_recurrent` places every
factor of length `ℓ ≤ 2ᵏ` inside every window of length `15·2ᵏ`, and
records that the *linear* specialization — a window of length `30ℓ`
for every `ℓ ≥ 1` — was left unformalized.  This file supplies it.

The whole content is the choice of `k`: with `k = ⌊log₂ ℓ⌋ + 1` one
has `ℓ < 2ᵏ` and `2ᵏ ≤ 2ℓ`, so the window `15·2ᵏ` is at most `30ℓ`.
Nothing about the sequence is used beyond the `2ᵏ`-window theorem.

* `thueMorseBit_uniformly_recurrent_linear` — every factor of length
  `ℓ ≥ 1` recurs inside every window of length `30ℓ`.
-/

set_option autoImplicit false

namespace Fabius

/-- **Linear recurrence gap**: a factor of length `ℓ ≥ 1` starting
anywhere occurs inside every window of length `30·ℓ`. -/
theorem thueMorseBit_uniformly_recurrent_linear (ℓ i₀ start : ℕ)
    (hℓ : 1 ≤ ℓ) :
    ∃ i, start ≤ i ∧ i + ℓ ≤ start + 30 * ℓ ∧
      ∀ j < ℓ, thueMorseBit (i + j) = thueMorseBit (i₀ + j) := by
  set k : ℕ := Nat.log 2 ℓ + 1 with hk
  have hle : ℓ ≤ 2 ^ k :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ℓ).le
  have hpow : 2 ^ k ≤ 2 * ℓ := by
    rw [hk, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  obtain ⟨i, hi₁, hi₂, hi₃⟩ :=
    thueMorseBit_uniformly_recurrent k ℓ i₀ start hle
  exact ⟨i, hi₁, by omega, hi₃⟩

end Fabius
