import FabiusFunction.QPochhammerIntegerIndex
import FabiusFunction.QPochhammerInfiniteBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Convergence of the bilateral series `₁ψ₁`

Ramanujan's bilateral series is

`₁ψ₁(a; b; q, z) = ∑_{n ∈ ℤ} (a;q)_n / (b;q)_n · z^n`,

with the integer-index symbols of `QPochhammerIntegerIndex`.  On the positive tail the
quotient `(a;q)_n/(b;q)_n` is bounded (both symbols converge, the denominator to a nonzero
limit), so the terms are dominated by a geometric series in `‖z‖`.  On the negative tail,
reversing the finite products gives

`(a;q)_{-m} / (b;q)_{-m} = (b/a)^m (q/b;q)_m / (q/a;q)_m`,

so the terms are dominated by a geometric series in `‖b/(az)‖`.  Hence the series converges
absolutely in the annulus `‖b/a‖ < ‖z‖ < 1`, in every complete normed field, whenever the
denominator factors `1 - bq^j` (`j ≥ 0`) and `1 - q^{j+1}/a` (`j ≥ 0`) are nonzero.

## Main declarations

* `onePsiOneTerm`, `onePsiOne`.
* `finiteQPochhammerZ_div_neg_natCast`: the negative-index quotient.
* `summable_onePsiOneTerm_nat`, `summable_onePsiOneTerm_neg`, `summable_onePsiOneTerm`.
* `summable_norm_onePsiOneTerm`: the same domination gives *absolute* convergence, i.e.
  summability of the norms, which in a general (possibly nonarchimedean) complete normed field
  is strictly stronger than `Summable`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- The `n`-th term of `₁ψ₁(a; b; q, z)`, `n ∈ ℤ`. -/
noncomputable def onePsiOneTerm (a b q z : 𝕜) (n : ℤ) : 𝕜 :=
  finiteQPochhammerZ a q n / finiteQPochhammerZ b q n * z ^ n

/-- **Ramanujan's bilateral series** `₁ψ₁(a; b; q, z) = ∑_{n ∈ ℤ} (a;q)_n/(b;q)_n z^n`. -/
noncomputable def onePsiOne (a b q z : 𝕜) : 𝕜 := ∑' n : ℤ, onePsiOneTerm a b q z n

/-- The negative-index quotient: `(a;q)_{-m}/(b;q)_{-m} = (b/a)^m (q/b;q)_m/(q/a;q)_m`. -/
theorem finiteQPochhammerZ_div_neg_natCast {a b q : 𝕜} (ha : a ≠ 0) (hb : b ≠ 0) (hq : q ≠ 0)
    (m : ℕ) :
    finiteQPochhammerZ a q (-m) / finiteQPochhammerZ b q (-m) =
      (b / a) ^ m * (finiteQPochhammerIn (q / b) q m / finiteQPochhammerIn (q / a) q m) := by
  rw [finiteQPochhammerZ_neg_natCast_eq ha hq, finiteQPochhammerZ_neg_natCast_eq hb hq]
  rcases eq_or_ne (finiteQPochhammerIn (q / a) q m) 0 with hpa | hpa
  · simp [hpa]
  rcases eq_or_ne (finiteQPochhammerIn (q / b) q m) 0 with hpb | hpb
  · simp [hpb]
  rw [div_pow, inv_pow, inv_pow]
  set A := a ^ m with hA
  set B := b ^ m with hB
  set s := (-1 : 𝕜) ^ m with hs
  set C := q ^ (m + 1).choose 2 with hC
  set P := finiteQPochhammerIn (q / a) q m with hP
  set P' := finiteQPochhammerIn (q / b) q m with hP'
  have hA0 : A ≠ 0 := pow_ne_zero _ ha
  have hB0 : B ≠ 0 := pow_ne_zero _ hb
  have hs0 : s ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hC0 : C ≠ 0 := pow_ne_zero _ hq
  field_simp

/-- The positive tail of `₁ψ₁` is dominated by a geometric series in `‖z‖`. -/
theorem summable_onePsiOneTerm_nat {a b q z : 𝕜} (hq : ‖q‖ < 1) (hb : qPochhammerInfIn b q ≠ 0)
    (hz : ‖z‖ < 1) : Summable fun n : ℕ => onePsiOneTerm a b q z n := by
  obtain ⟨K, _, hK⟩ := exists_norm_finiteQPochhammerIn_div_le a hq hb
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left K)
    fun n => ?_
  rw [onePsiOneTerm, finiteQPochhammerZ_natCast, finiteQPochhammerZ_natCast, zpow_natCast,
    norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hK n) (pow_nonneg (norm_nonneg z) n)

/-- The negative tail of `₁ψ₁` is dominated by a geometric series in `‖b/(az)‖`. -/
theorem summable_onePsiOneTerm_neg {a b q z : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (haq : qPochhammerInfIn (q / a) q ≠ 0) (hbz : ‖b / a‖ < ‖z‖) :
    Summable fun n : ℕ => onePsiOneTerm a b q z (-n) := by
  obtain ⟨K, _, hK⟩ := exists_norm_finiteQPochhammerIn_div_le (q / b) hq haq
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hz_pos : 0 < ‖z‖ := (norm_nonneg _).trans_lt hbz
  have hbz' : ‖b‖ < ‖a‖ * ‖z‖ := by
    rw [norm_div, div_lt_iff₀ ha_pos, mul_comm] at hbz
    exact hbz
  have hr : ‖b / (a * z)‖ < 1 := by
    rw [norm_div, norm_mul, div_lt_one (mul_pos ha_pos hz_pos)]
    exact hbz'
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hr).mul_left K)
    fun m => ?_
  have hpow : (b / a) ^ m * (z ^ m)⁻¹ = (b / (a * z)) ^ m := by
    rw [div_pow, div_pow, mul_pow, ← div_eq_mul_inv, div_div]
  rw [onePsiOneTerm, finiteQPochhammerZ_div_neg_natCast ha0 hb0 hq0, zpow_neg, zpow_natCast,
    mul_right_comm, hpow, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK m) (pow_nonneg (norm_nonneg _) m)

/-- **Convergence annulus of `₁ψ₁`**: for `‖q‖ < 1`, `q ≠ 0`, nonzero `a, b` with `bq^j ≠ 1` and
`q^{j+1}/a ≠ 1` for all `j ≥ 0`, the bilateral series converges absolutely for
`‖b/a‖ < ‖z‖ < 1`. -/
theorem summable_onePsiOneTerm {a b q z : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hb : ∀ j : ℕ, b * q ^ j ≠ 1) (ha : ∀ j : ℕ, q / a * q ^ j ≠ 1)
    (hbz : ‖b / a‖ < ‖z‖) (hz : ‖z‖ < 1) : Summable (onePsiOneTerm a b q z) :=
  Summable.of_nat_of_neg (summable_onePsiOneTerm_nat hq (qPochhammerInfIn_ne_zero b hq hb) hz)
    (summable_onePsiOneTerm_neg hq hq0 ha0 hb0 (qPochhammerInfIn_ne_zero _ hq ha) hbz)

/-- The positive tail converges **absolutely**. -/
theorem summable_norm_onePsiOneTerm_nat {a b q z : 𝕜} (hq : ‖q‖ < 1)
    (hb : qPochhammerInfIn b q ≠ 0) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖onePsiOneTerm a b q z n‖ := by
  obtain ⟨K, _, hK⟩ := exists_norm_finiteQPochhammerIn_div_le a hq hb
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left K)
    fun n => ?_
  rw [norm_norm, onePsiOneTerm, finiteQPochhammerZ_natCast, finiteQPochhammerZ_natCast,
    zpow_natCast, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hK n) (pow_nonneg (norm_nonneg z) n)

/-- The negative tail converges **absolutely**. -/
theorem summable_norm_onePsiOneTerm_neg {a b q z : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (haq : qPochhammerInfIn (q / a) q ≠ 0) (hbz : ‖b / a‖ < ‖z‖) :
    Summable fun n : ℕ => ‖onePsiOneTerm a b q z (-n)‖ := by
  obtain ⟨K, _, hK⟩ := exists_norm_finiteQPochhammerIn_div_le (q / b) hq haq
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hz_pos : 0 < ‖z‖ := (norm_nonneg _).trans_lt hbz
  have hbz' : ‖b‖ < ‖a‖ * ‖z‖ := by
    rw [norm_div, div_lt_iff₀ ha_pos, mul_comm] at hbz
    exact hbz
  have hr : ‖b / (a * z)‖ < 1 := by
    rw [norm_div, norm_mul, div_lt_one (mul_pos ha_pos hz_pos)]
    exact hbz'
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hr).mul_left K)
    fun m => ?_
  have hpow : (b / a) ^ m * (z ^ m)⁻¹ = (b / (a * z)) ^ m := by
    rw [div_pow, div_pow, mul_pow, ← div_eq_mul_inv, div_div]
  rw [norm_norm, onePsiOneTerm, finiteQPochhammerZ_div_neg_natCast ha0 hb0 hq0, zpow_neg,
    zpow_natCast, mul_right_comm, hpow, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK m) (pow_nonneg (norm_nonneg _) m)

/-- **Absolute convergence of `₁ψ₁` on its annulus.**  Under the hypotheses of
`summable_onePsiOneTerm` the norms of the terms are summable, so the bilateral series converges
absolutely, not merely unconditionally. -/
theorem summable_norm_onePsiOneTerm {a b q z : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hb : ∀ j : ℕ, b * q ^ j ≠ 1) (ha : ∀ j : ℕ, q / a * q ^ j ≠ 1)
    (hbz : ‖b / a‖ < ‖z‖) (hz : ‖z‖ < 1) :
    Summable fun n : ℤ => ‖onePsiOneTerm a b q z n‖ :=
  Summable.of_nat_of_neg
    (summable_norm_onePsiOneTerm_nat hq (qPochhammerInfIn_ne_zero b hq hb) hz)
    (summable_norm_onePsiOneTerm_neg hq hq0 ha0 hb0 (qPochhammerInfIn_ne_zero _ hq ha) hbz)

end Fabius
