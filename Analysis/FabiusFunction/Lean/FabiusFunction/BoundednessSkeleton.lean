import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log

/-!
# The (Q3) boundedness skeleton: dyadic control of a monotone mass

The audits' two-sided bounded Cesàro theorem — *"the ratio is
eventually confined to a compact subinterval of `(0,∞)`"* — reduced to
its limit-theoretic core: if a **monotone** cumulative mass `G`
satisfies the dyadic-ray normalization `G(2ᴷ)/2ᴷ → A > 0` (which the
RPF layer supplies for `G(t) = ∫_{t₀}^t |f|/g₁`, with
`A = A₁ = 0.09126612…`), then for all large real `t`,

`A/4 ≤ G(t)/t ≤ 3A`.

Monotonicity sandwiches every `t ∈ [2ᴷ, 2ᴷ⁺¹)` between the two
adjacent dyadic values, each within a factor `2` of its normalization
— no within-shell information needed.  This is the audit's
`(Q3)`-boundedness (`thm:audit-answer` (i)), modulo the dyadic limit.

* `eventually_bounded_of_monotone_of_dyadic` — the sandwich.
-/

set_option autoImplicit false

open Filter

namespace Fabius

/-- **The (Q3) sandwich**: a monotone mass with dyadic-ray
normalization `G(2ᴷ)/2ᴷ → A > 0` has `A/4 ≤ G(t)/t ≤ 3A` for all
large `t`. -/
theorem eventually_bounded_of_monotone_of_dyadic {G : ℝ → ℝ} {A : ℝ}
    (hmono : Monotone G) (hA : 0 < A)
    (hdy : Tendsto (fun K : ℕ => G ((2:ℝ) ^ K) / 2 ^ K) atTop (nhds A)) :
    ∀ᶠ t : ℝ in atTop, A / 4 ≤ G t / t ∧ G t / t ≤ 3 * A := by
  have hlow : ∀ᶠ K : ℕ in atTop, A / 2 ≤ G ((2:ℝ) ^ K) / 2 ^ K :=
    hdy.eventually (eventually_ge_nhds (by linarith))
  have hup : ∀ᶠ K : ℕ in atTop, G ((2:ℝ) ^ K) / 2 ^ K ≤ 3 * A / 2 :=
    hdy.eventually (eventually_le_nhds (by linarith))
  obtain ⟨K₀, hK₀⟩ := (hlow.and hup).exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop ((2:ℝ) ^ K₀),
    eventually_ge_atTop (1:ℝ)] with t ht2K ht1
  -- locate t in its dyadic block via Nat.log of the floor
  set n : ℕ := ⌊t⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast ht1)
  set K : ℕ := Nat.log 2 n with hK
  have h2Kn : (2:ℕ) ^ K ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hn2K : n < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2Kt : (2:ℝ) ^ K ≤ t := by
    calc ((2:ℝ) ^ K) = ((2 ^ K : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (n : ℝ) := by exact_mod_cast h2Kn
      _ ≤ t := Nat.floor_le (by linarith)
  have ht2K1 : t < (2:ℝ) ^ (K + 1) := by
    calc t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
      _ ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast hn2K
      _ = (2:ℝ) ^ (K + 1) := by push_cast; ring
  -- K is at least K₀
  have hKK₀ : K₀ ≤ K := by
    have h2K₀n : (2:ℕ) ^ K₀ ≤ n := by
      have : ((2 ^ K₀ : ℕ) : ℝ) ≤ t := by
        calc ((2 ^ K₀ : ℕ) : ℝ) = (2:ℝ) ^ K₀ := by push_cast; ring
          _ ≤ t := ht2K
      exact Nat.le_floor (by exact_mod_cast this)
    calc K₀ = Nat.log 2 (2 ^ K₀) := (Nat.log_pow (by norm_num) K₀).symm
      _ ≤ Nat.log 2 n := Nat.log_mono_right h2K₀n
  have hbandK := hK₀ K hKK₀
  have hbandK1 := hK₀ (K + 1) (by omega)
  have hpK : (0:ℝ) < 2 ^ K := by positivity
  have hpK1 : (0:ℝ) < 2 ^ (K + 1) := by positivity
  have ht0 : (0:ℝ) < t := by linarith
  have hps : (2:ℝ) ^ (K + 1) = 2 * 2 ^ K := by
    rw [pow_succ]
    ring
  have hb1 : A / 2 * 2 ^ K ≤ G ((2:ℝ) ^ K) := (le_div_iff₀ hpK).mp hbandK.1
  have hb2 : G ((2:ℝ) ^ (K + 1)) ≤ 3 * A / 2 * 2 ^ (K + 1) :=
    (div_le_iff₀ hpK1).mp hbandK1.2
  have hmono1 : G ((2:ℝ) ^ K) ≤ G t := hmono h2Kt
  have hmono2 : G t ≤ G ((2:ℝ) ^ (K + 1)) := hmono ht2K1.le
  constructor
  · rw [le_div_iff₀ ht0]
    nlinarith [hb1, hmono1, ht2K1.le, hps, hA.le, hpK.le]
  · rw [div_le_iff₀ ht0]
    nlinarith [hb2, hmono2, h2Kt, hps, hA.le, hpK.le]

end Fabius
