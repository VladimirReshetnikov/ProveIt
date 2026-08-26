import FabiusFunction.PeriodicMean
import FabiusFunction.NegativeLaplaceDerivatives
import FabiusFunction.Existence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Taylor

/-!
# Higher regularity of the negative-Laplace periodic correction

This module differentiates the exponentially small forward tail termwise
through order four.  Superexponential majorants give uniform convergence on
each positive half-line.  Combining this with the compactly supported Fabius
Laplace integral proves that the exact periodic correction and its zero-mean
normalization are C⁴.

The module also exposes one-periodicity and global boundedness for the first
two derivatives of the normalized correction, the regularity input needed by
the sharp dyadic phase expansion.  The four termwise derivative tails are
identified explicitly with successive ordinary derivatives, giving later
all-orders arguments a reusable bridge from `HasDerivAt` to `deriv`.
The elementary dyadic-exponential derivative, monotonicity, nonunit, and
positive-denominator facts are exposed here for reuse by all later periodic
modules.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff Topology
open Set Filter

namespace Fabius

lemma summable_two_pow_mul_exp_neg_two_pow
    (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Summable (fun n : ℕ =>
      (2 : ℝ) ^ (k * n) * Real.exp (-(a * (2 : ℝ) ^ n))) := by
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · filter_upwards with n
    positivity
  · have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    have hneg : Tendsto (fun n : ℕ => -(a * (2 : ℝ) ^ n)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hpow.const_mul_atTop ha)
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(a * (2 : ℝ) ^ n)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg
    have hconst : Tendsto (fun _ : ℕ => (2 : ℝ) ^ k) atTop
        (𝓝 ((2 : ℝ) ^ k)) := tendsto_const_nhds
    have hprod := hconst.mul hexp
    simpa only [mul_zero] using hprod.congr' (Eventually.of_forall fun n => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      symm
      rw [div_eq_iff (by positivity)]
      rw [Nat.mul_add, pow_add]
      have hpow_succ : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
        rw [pow_succ']
      rw [hpow_succ]
      rw [show -(a * (2 * (2 : ℝ) ^ n)) =
          -(a * (2 : ℝ) ^ n) + -(a * (2 : ℝ) ^ n) by ring,
        Real.exp_add]
      ring)

lemma summable_forward_derivative_majorant
    (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Summable (fun n : ℕ =>
      ((2 : ℝ) ^ n) ^ k * Real.exp (-(a * (2 : ℝ) ^ n))) := by
  convert summable_two_pow_mul_exp_neg_two_pow a ha k using 1
  ext n
  rw [← pow_mul, Nat.mul_comm n k]

noncomputable def negativeLaplaceForwardTermFirst (s : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * Real.exp (-(s * (2 : ℝ) ^ n)) /
    (1 - Real.exp (-(s * (2 : ℝ) ^ n)))

noncomputable def negativeLaplaceForwardTermSecond (s : ℝ) (n : ℕ) : ℝ :=
  -(((2 : ℝ) ^ n) ^ 2 * Real.exp (-(s * (2 : ℝ) ^ n)) /
    (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 2)

noncomputable def negativeLaplaceForwardTermThird (s : ℝ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n) ^ 3 * Real.exp (-(s * (2 : ℝ) ^ n)) *
      (1 + Real.exp (-(s * (2 : ℝ) ^ n))) /
    (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 3

noncomputable def negativeLaplaceForwardTermFourth (s : ℝ) (n : ℕ) : ℝ :=
  -(((2 : ℝ) ^ n) ^ 4 * Real.exp (-(s * (2 : ℝ) ^ n)) *
      (1 + 4 * Real.exp (-(s * (2 : ℝ) ^ n)) +
        Real.exp (-(s * (2 : ℝ) ^ n)) ^ 2) /
    (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 4)

/-- The forward dyadic exponential is nonunit at every nonzero scale. -/
theorem exp_neg_mul_two_pow_ne_one (s : ℝ) (hs : s ≠ 0) (n : ℕ) :
    Real.exp (-(s * (2 : ℝ) ^ n)) ≠ 1 := by
  rw [ne_eq, Real.exp_eq_one_iff]
  exact neg_ne_zero.mpr (mul_ne_zero hs (by positivity))

/-- Derivative in the scale of the forward dyadic exponential. -/
theorem hasDerivAt_exp_neg_mul_two_pow (s : ℝ) (n : ℕ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(x * (2 : ℝ) ^ n)))
      (-((2 : ℝ) ^ n) * Real.exp (-(s * (2 : ℝ) ^ n))) s := by
  simpa only [Pi.neg_apply, id_eq, one_mul, mul_comm] using
    (((hasDerivAt_id s).mul_const ((2 : ℝ) ^ n)).neg.exp)

lemma negativeLaplaceForwardTerm_hasDerivAt
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    HasDerivAt (fun x : ℝ => negativeLaplaceForwardTerm x n)
      (negativeLaplaceForwardTermFirst s n) s := by
  let a := (2 : ℝ) ^ n
  let z := Real.exp (-(s * a))
  have hz : HasDerivAt (fun x : ℝ => Real.exp (-(x * a))) (-a * z) s := by
    simpa [a, z] using hasDerivAt_exp_neg_mul_two_pow s n
  have hu := (hasDerivAt_const s (1 : ℝ)).sub hz
  have hune : 1 - z ≠ 0 := sub_ne_zero.mpr (by
    simpa [a, z] using (exp_neg_mul_two_pow_ne_one s hs.ne' n).symm)
  have hlog := hu.log hune
  simpa [negativeLaplaceForwardTerm, negativeLaplaceForwardTermFirst, a, z,
    sub_eq_add_neg, mul_comm] using hlog

lemma negativeLaplaceForwardTermFirst_hasDerivAt
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    HasDerivAt (fun x : ℝ => negativeLaplaceForwardTermFirst x n)
      (negativeLaplaceForwardTermSecond s n) s := by
  let a := (2 : ℝ) ^ n
  let z := Real.exp (-(s * a))
  have hz : HasDerivAt (fun x : ℝ => Real.exp (-(x * a))) (-a * z) s := by
    simpa [a, z] using hasDerivAt_exp_neg_mul_two_pow s n
  have hu := (hasDerivAt_const s (1 : ℝ)).sub hz
  have hune : 1 - z ≠ 0 := sub_ne_zero.mpr (by
    simpa [a, z] using (exp_neg_mul_two_pow_ne_one s hs.ne' n).symm)
  have h := (hz.const_mul a).div hu hune
  change HasDerivAt
    (fun x : ℝ => a * Real.exp (-(x * a)) / (1 - Real.exp (-(x * a))))
    (-(a ^ 2 * z / (1 - z) ^ 2)) s
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.sub_apply]
    rw [show Real.exp (-(s * a)) = z by rfl]
    field_simp [hune]
    ring
  · filter_upwards with x
    rfl

lemma negativeLaplaceForwardTermSecond_hasDerivAt
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    HasDerivAt (fun x : ℝ => negativeLaplaceForwardTermSecond x n)
      (negativeLaplaceForwardTermThird s n) s := by
  let a := (2 : ℝ) ^ n
  let z := Real.exp (-(s * a))
  have hz : HasDerivAt (fun x : ℝ => Real.exp (-(x * a))) (-a * z) s := by
    simpa [a, z] using hasDerivAt_exp_neg_mul_two_pow s n
  have hu := (hasDerivAt_const s (1 : ℝ)).sub hz
  have hune : 1 - z ≠ 0 := sub_ne_zero.mpr (by
    simpa [a, z] using (exp_neg_mul_two_pow_ne_one s hs.ne' n).symm)
  have hbase := (((hz.const_mul (a ^ 2)).div (hu.pow 2) (pow_ne_zero 2 hune)).neg)
  change HasDerivAt
    (fun x : ℝ => -(a ^ 2 * Real.exp (-(x * a)) /
      (1 - Real.exp (-(x * a))) ^ 2))
    (a ^ 3 * z * (1 + z) / (1 - z) ^ 3) s
  refine (hbase.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.sub_apply, Pi.pow_apply]
    rw [show Real.exp (-(s * a)) = z by rfl]
    field_simp [hune]
    ring
  · filter_upwards with x
    rfl

lemma negativeLaplaceForwardTermThird_hasDerivAt
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    HasDerivAt (fun x : ℝ => negativeLaplaceForwardTermThird x n)
      (negativeLaplaceForwardTermFourth s n) s := by
  let a := (2 : ℝ) ^ n
  let z := Real.exp (-(s * a))
  have hz : HasDerivAt (fun x : ℝ => Real.exp (-(x * a))) (-a * z) s := by
    simpa [a, z] using hasDerivAt_exp_neg_mul_two_pow s n
  have hu := (hasDerivAt_const s (1 : ℝ)).sub hz
  have hune : 1 - z ≠ 0 := sub_ne_zero.mpr (by
    simpa [a, z] using (exp_neg_mul_two_pow_ne_one s hs.ne' n).symm)
  have hnum := ((hz.const_mul (a ^ 3)).mul
    ((hasDerivAt_const s (1 : ℝ)).add hz))
  have hbase := hnum.div (hu.pow 3) (pow_ne_zero 3 hune)
  change HasDerivAt
    (fun x : ℝ => a ^ 3 * Real.exp (-(x * a)) *
      (1 + Real.exp (-(x * a))) / (1 - Real.exp (-(x * a))) ^ 3)
    (-(a ^ 4 * z * (1 + 4 * z + z ^ 2) / (1 - z) ^ 4)) s
  refine (hbase.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    rw [show Real.exp (-(s * a)) = z by rfl]
    field_simp [hune]
    ring
  · filter_upwards with x
    rfl

/-- The forward dyadic exponential is antitone in its scale. -/
theorem exp_neg_mul_two_pow_le_of_le
    {a s : ℝ} (has : a ≤ s) (n : ℕ) :
    Real.exp (-(s * (2 : ℝ) ^ n)) ≤
      Real.exp (-(a * (2 : ℝ) ^ n)) := by
  apply Real.exp_le_exp.mpr
  have hn : 0 < (2 : ℝ) ^ n := by positivity
  nlinarith

private lemma forward_denominator_le
    (a s : ℝ) (has : a ≤ s) (n : ℕ) :
    1 - Real.exp (-(a * (2 : ℝ) ^ n)) ≤
      1 - Real.exp (-(s * (2 : ℝ) ^ n)) :=
  sub_le_sub_left (exp_neg_mul_two_pow_le_of_le has n) 1

/-- The forward dyadic denominator is positive at every positive scale. -/
theorem one_sub_exp_neg_mul_two_pow_pos (s : ℝ) (hs : 0 < s) (n : ℕ) :
    0 < 1 - Real.exp (-(s * (2 : ℝ) ^ n)) := by
  rw [sub_pos, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  exact neg_lt_zero.mpr (mul_pos hs (by positivity))

lemma norm_negativeLaplaceForwardTermFirst_le
    (a s : ℝ) (ha : 0 < a) (has : a ≤ s) (n : ℕ) :
    ‖negativeLaplaceForwardTermFirst s n‖ ≤
      (1 / (1 - Real.exp (-a))) *
        (((2 : ℝ) ^ n) ^ 1 * Real.exp (-(a * (2 : ℝ) ^ n))) := by
  have hs : 0 < s := ha.trans_le has
  have hz := exp_neg_mul_two_pow_le_of_le has n
  have hza : Real.exp (-(a * (2 : ℝ) ^ n)) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    have hn : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hd := forward_denominator_le a s has n
  have hd' : 1 - Real.exp (-a) ≤
      1 - Real.exp (-(s * (2 : ℝ) ^ n)) :=
    (sub_le_sub_left hza 1).trans hd
  have hdpos : 0 < 1 - Real.exp (-a) := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdspos := one_sub_exp_neg_mul_two_pow_pos s hs n
  unfold negativeLaplaceForwardTermFirst
  rw [Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (by positivity : 0 < (2 : ℝ) ^ n),
    abs_of_pos (Real.exp_pos _), abs_of_pos hdspos]
  calc
    (2 : ℝ) ^ n * Real.exp (-(s * (2 : ℝ) ^ n)) /
          (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ≤
        (2 : ℝ) ^ n * Real.exp (-(a * (2 : ℝ) ^ n)) /
          (1 - Real.exp (-a)) := by
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hz (by positivity))
        hdpos hd'
    _ = (1 / (1 - Real.exp (-a))) *
        (((2 : ℝ) ^ n) ^ 1 * Real.exp (-(a * (2 : ℝ) ^ n))) := by
      simp
      ring

lemma norm_negativeLaplaceForwardTermSecond_le
    (a s : ℝ) (ha : 0 < a) (has : a ≤ s) (n : ℕ) :
    ‖negativeLaplaceForwardTermSecond s n‖ ≤
      (1 / (1 - Real.exp (-a)) ^ 2) *
        (((2 : ℝ) ^ n) ^ 2 * Real.exp (-(a * (2 : ℝ) ^ n))) := by
  have hs : 0 < s := ha.trans_le has
  have hz := exp_neg_mul_two_pow_le_of_le has n
  have hza : Real.exp (-(a * (2 : ℝ) ^ n)) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    have hn : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hd := forward_denominator_le a s has n
  have hd' : 1 - Real.exp (-a) ≤
      1 - Real.exp (-(s * (2 : ℝ) ^ n)) :=
    (sub_le_sub_left hza 1).trans hd
  have hdpos : 0 < 1 - Real.exp (-a) := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdspos := one_sub_exp_neg_mul_two_pow_pos s hs n
  have hdpow : (1 - Real.exp (-a)) ^ 2 ≤
      (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 2 :=
    pow_le_pow_left₀ hdpos.le hd' 2
  unfold negativeLaplaceForwardTermSecond
  rw [Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos (mul_pos (by positivity)
    (Real.exp_pos _)) (pow_pos hdspos 2))]
  calc
    ((2 : ℝ) ^ n) ^ 2 * Real.exp (-(s * (2 : ℝ) ^ n)) /
          (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 2 ≤
        ((2 : ℝ) ^ n) ^ 2 * Real.exp (-(a * (2 : ℝ) ^ n)) /
          (1 - Real.exp (-a)) ^ 2 := by
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hz (by positivity))
        (pow_pos hdpos 2) hdpow
    _ = (1 / (1 - Real.exp (-a)) ^ 2) *
        (((2 : ℝ) ^ n) ^ 2 * Real.exp (-(a * (2 : ℝ) ^ n))) := by ring

lemma norm_negativeLaplaceForwardTermThird_le
    (a s : ℝ) (ha : 0 < a) (has : a ≤ s) (n : ℕ) :
    ‖negativeLaplaceForwardTermThird s n‖ ≤
      (2 / (1 - Real.exp (-a)) ^ 3) *
        (((2 : ℝ) ^ n) ^ 3 * Real.exp (-(a * (2 : ℝ) ^ n))) := by
  have hs : 0 < s := ha.trans_le has
  have hz := exp_neg_mul_two_pow_le_of_le has n
  have hza : Real.exp (-(a * (2 : ℝ) ^ n)) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    have hn : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hzs_one : Real.exp (-(s * (2 : ℝ) ^ n)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact (neg_nonpos.mpr (mul_nonneg hs.le (by positivity)))
  have hd := forward_denominator_le a s has n
  have hd' : 1 - Real.exp (-a) ≤
      1 - Real.exp (-(s * (2 : ℝ) ^ n)) :=
    (sub_le_sub_left hza 1).trans hd
  have hdpos : 0 < 1 - Real.exp (-a) := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdspos := one_sub_exp_neg_mul_two_pow_pos s hs n
  have hdpow : (1 - Real.exp (-a)) ^ 3 ≤
      (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 3 :=
    pow_le_pow_left₀ hdpos.le hd' 3
  have hnum : ((2 : ℝ) ^ n) ^ 3 * Real.exp (-(s * (2 : ℝ) ^ n)) *
        (1 + Real.exp (-(s * (2 : ℝ) ^ n))) ≤
      2 * (((2 : ℝ) ^ n) ^ 3 * Real.exp (-(a * (2 : ℝ) ^ n))) := by
    calc
      ((2 : ℝ) ^ n) ^ 3 * Real.exp (-(s * (2 : ℝ) ^ n)) *
          (1 + Real.exp (-(s * (2 : ℝ) ^ n))) ≤
        ((2 : ℝ) ^ n) ^ 3 * Real.exp (-(a * (2 : ℝ) ^ n)) * 2 := by
          gcongr
          linarith
      _ = 2 * (((2 : ℝ) ^ n) ^ 3 * Real.exp (-(a * (2 : ℝ) ^ n))) := by ring
  unfold negativeLaplaceForwardTermThird
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (mul_pos
    (mul_pos (by positivity) (Real.exp_pos _)) (by positivity)) (pow_pos hdspos 3))]
  calc
    ((2 : ℝ) ^ n) ^ 3 * Real.exp (-(s * (2 : ℝ) ^ n)) *
          (1 + Real.exp (-(s * (2 : ℝ) ^ n))) /
          (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 3 ≤
        (2 * (((2 : ℝ) ^ n) ^ 3 * Real.exp (-(a * (2 : ℝ) ^ n)))) /
          (1 - Real.exp (-a)) ^ 3 := by
      exact div_le_div₀ (by positivity) hnum (pow_pos hdpos 3) hdpow
    _ = (2 / (1 - Real.exp (-a)) ^ 3) *
        (((2 : ℝ) ^ n) ^ 3 * Real.exp (-(a * (2 : ℝ) ^ n))) := by ring

lemma norm_negativeLaplaceForwardTermFourth_le
    (a s : ℝ) (ha : 0 < a) (has : a ≤ s) (n : ℕ) :
    ‖negativeLaplaceForwardTermFourth s n‖ ≤
      (6 / (1 - Real.exp (-a)) ^ 4) *
        (((2 : ℝ) ^ n) ^ 4 * Real.exp (-(a * (2 : ℝ) ^ n))) := by
  have hs : 0 < s := ha.trans_le has
  have hz := exp_neg_mul_two_pow_le_of_le has n
  have hza : Real.exp (-(a * (2 : ℝ) ^ n)) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    have hn : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  let z := Real.exp (-(s * (2 : ℝ) ^ n))
  have hz0 : 0 ≤ z := Real.exp_nonneg _
  have hz1 : z ≤ 1 := by
    dsimp [z]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact neg_nonpos.mpr (mul_nonneg hs.le (by positivity))
  have hzpoly : 1 + 4 * z + z ^ 2 ≤ 6 := by
    have hzsq : z ^ 2 ≤ 1 := by nlinarith [mul_self_le_mul_self hz0 hz1]
    nlinarith
  have hd := forward_denominator_le a s has n
  have hd' : 1 - Real.exp (-a) ≤
      1 - Real.exp (-(s * (2 : ℝ) ^ n)) :=
    (sub_le_sub_left hza 1).trans hd
  have hdpos : 0 < 1 - Real.exp (-a) := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdspos := one_sub_exp_neg_mul_two_pow_pos s hs n
  have hdpow : (1 - Real.exp (-a)) ^ 4 ≤
      (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 4 :=
    pow_le_pow_left₀ hdpos.le hd' 4
  have hnum : ((2 : ℝ) ^ n) ^ 4 * z * (1 + 4 * z + z ^ 2) ≤
      6 * (((2 : ℝ) ^ n) ^ 4 * Real.exp (-(a * (2 : ℝ) ^ n))) := by
    calc
      ((2 : ℝ) ^ n) ^ 4 * z * (1 + 4 * z + z ^ 2) ≤
          ((2 : ℝ) ^ n) ^ 4 * Real.exp (-(a * (2 : ℝ) ^ n)) * 6 := by
        gcongr
      _ = 6 * (((2 : ℝ) ^ n) ^ 4 * Real.exp (-(a * (2 : ℝ) ^ n))) := by ring
  unfold negativeLaplaceForwardTermFourth
  rw [show Real.exp (-(s * (2 : ℝ) ^ n)) = z by rfl]
  rw [Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos (mul_pos
    (mul_pos (by positivity) (Real.exp_pos _)) (by positivity)) (pow_pos hdspos 4))]
  calc
    ((2 : ℝ) ^ n) ^ 4 * z * (1 + 4 * z + z ^ 2) /
          (1 - z) ^ 4 ≤
        (6 * (((2 : ℝ) ^ n) ^ 4 * Real.exp (-(a * (2 : ℝ) ^ n)))) /
          (1 - Real.exp (-a)) ^ 4 := by
      exact div_le_div₀ (by positivity) hnum (pow_pos hdpos 4) (by simpa [z] using hdpow)
    _ = (6 / (1 - Real.exp (-a)) ^ 4) *
        (((2 : ℝ) ^ n) ^ 4 * Real.exp (-(a * (2 : ℝ) ^ n))) := by ring

noncomputable def negativeLaplaceForwardTailFirst (s : ℝ) : ℝ :=
  ∑' n : ℕ, negativeLaplaceForwardTermFirst s n

noncomputable def negativeLaplaceForwardTailSecond (s : ℝ) : ℝ :=
  ∑' n : ℕ, negativeLaplaceForwardTermSecond s n

noncomputable def negativeLaplaceForwardTailThird (s : ℝ) : ℝ :=
  ∑' n : ℕ, negativeLaplaceForwardTermThird s n

noncomputable def negativeLaplaceForwardTailFourth (s : ℝ) : ℝ :=
  ∑' n : ℕ, negativeLaplaceForwardTermFourth s n

theorem summable_negativeLaplaceForwardTermFirst (s : ℝ) (hs : 0 < s) :
    Summable (negativeLaplaceForwardTermFirst s) := by
  have hmajor := (summable_forward_derivative_majorant s hs 1).mul_left
    (1 / (1 - Real.exp (-s)))
  exact hmajor.of_norm_bounded
    (norm_negativeLaplaceForwardTermFirst_le s s hs le_rfl)

theorem summable_negativeLaplaceForwardTermSecond (s : ℝ) (hs : 0 < s) :
    Summable (negativeLaplaceForwardTermSecond s) := by
  have hmajor := (summable_forward_derivative_majorant s hs 2).mul_left
    (1 / (1 - Real.exp (-s)) ^ 2)
  exact hmajor.of_norm_bounded
    (norm_negativeLaplaceForwardTermSecond_le s s hs le_rfl)

theorem summable_negativeLaplaceForwardTermThird (s : ℝ) (hs : 0 < s) :
    Summable (negativeLaplaceForwardTermThird s) := by
  have hmajor := (summable_forward_derivative_majorant s hs 3).mul_left
    (2 / (1 - Real.exp (-s)) ^ 3)
  exact hmajor.of_norm_bounded
    (norm_negativeLaplaceForwardTermThird_le s s hs le_rfl)

theorem summable_negativeLaplaceForwardTermFourth (s : ℝ) (hs : 0 < s) :
    Summable (negativeLaplaceForwardTermFourth s) := by
  have hmajor := (summable_forward_derivative_majorant s hs 4).mul_left
    (6 / (1 - Real.exp (-s)) ^ 4)
  exact hmajor.of_norm_bounded
    (norm_negativeLaplaceForwardTermFourth_le s s hs le_rfl)

theorem negativeLaplaceForwardTail_hasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt negativeLaplaceForwardTail
      (negativeLaplaceForwardTailFirst s) s := by
  let a := s / 2
  let u : ℕ → ℝ := fun n =>
    (1 / (1 - Real.exp (-a))) *
      (((2 : ℝ) ^ n) ^ 1 * Real.exp (-(a * (2 : ℝ) ^ n)))
  have ha : 0 < a := by dsimp [a]; positivity
  have hu : Summable u :=
    (summable_forward_derivative_majorant a ha 1).mul_left
      (1 / (1 - Real.exp (-a)))
  change HasDerivAt
    (fun y : ℝ => ∑' n : ℕ, negativeLaplaceForwardTerm y n)
    (∑' n : ℕ, negativeLaplaceForwardTermFirst s n) s
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTerm y n)
    (g' := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermFirst y n)
    (u := u) (t := Ioi a) (y₀ := s) (y := s)
    hu isOpen_Ioi isPreconnected_Ioi ?_ ?_ ?_ ?_ ?_
  · intro n y hy
    exact negativeLaplaceForwardTerm_hasDerivAt y (ha.trans hy) n
  · intro n y hy
    exact norm_negativeLaplaceForwardTermFirst_le a y ha hy.le n
  · exact show a < s by dsimp [a]; linarith
  · exact summable_negativeLaplaceForwardTerm s hs
  · exact show a < s by dsimp [a]; linarith

theorem negativeLaplaceForwardTailFirst_hasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt negativeLaplaceForwardTailFirst
      (negativeLaplaceForwardTailSecond s) s := by
  let a := s / 2
  let u : ℕ → ℝ := fun n =>
    (1 / (1 - Real.exp (-a)) ^ 2) *
      (((2 : ℝ) ^ n) ^ 2 * Real.exp (-(a * (2 : ℝ) ^ n)))
  have ha : 0 < a := by dsimp [a]; positivity
  have hu : Summable u :=
    (summable_forward_derivative_majorant a ha 2).mul_left
      (1 / (1 - Real.exp (-a)) ^ 2)
  change HasDerivAt
    (fun y : ℝ => ∑' n : ℕ, negativeLaplaceForwardTermFirst y n)
    (∑' n : ℕ, negativeLaplaceForwardTermSecond s n) s
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermFirst y n)
    (g' := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermSecond y n)
    (u := u) (t := Ioi a) (y₀ := s) (y := s)
    hu isOpen_Ioi isPreconnected_Ioi ?_ ?_ ?_ ?_ ?_
  · intro n y hy
    exact negativeLaplaceForwardTermFirst_hasDerivAt y (ha.trans hy) n
  · intro n y hy
    exact norm_negativeLaplaceForwardTermSecond_le a y ha hy.le n
  · exact show a < s by dsimp [a]; linarith
  · exact summable_negativeLaplaceForwardTermFirst s hs
  · exact show a < s by dsimp [a]; linarith

theorem negativeLaplaceForwardTailSecond_hasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt negativeLaplaceForwardTailSecond
      (negativeLaplaceForwardTailThird s) s := by
  let a := s / 2
  let u : ℕ → ℝ := fun n =>
    (2 / (1 - Real.exp (-a)) ^ 3) *
      (((2 : ℝ) ^ n) ^ 3 * Real.exp (-(a * (2 : ℝ) ^ n)))
  have ha : 0 < a := by dsimp [a]; positivity
  have hu : Summable u :=
    (summable_forward_derivative_majorant a ha 3).mul_left
      (2 / (1 - Real.exp (-a)) ^ 3)
  change HasDerivAt
    (fun y : ℝ => ∑' n : ℕ, negativeLaplaceForwardTermSecond y n)
    (∑' n : ℕ, negativeLaplaceForwardTermThird s n) s
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermSecond y n)
    (g' := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermThird y n)
    (u := u) (t := Ioi a) (y₀ := s) (y := s)
    hu isOpen_Ioi isPreconnected_Ioi ?_ ?_ ?_ ?_ ?_
  · intro n y hy
    exact negativeLaplaceForwardTermSecond_hasDerivAt y (ha.trans hy) n
  · intro n y hy
    exact norm_negativeLaplaceForwardTermThird_le a y ha hy.le n
  · exact show a < s by dsimp [a]; linarith
  · exact summable_negativeLaplaceForwardTermSecond s hs
  · exact show a < s by dsimp [a]; linarith

theorem negativeLaplaceForwardTailThird_hasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt negativeLaplaceForwardTailThird
      (negativeLaplaceForwardTailFourth s) s := by
  let a := s / 2
  let u : ℕ → ℝ := fun n =>
    (6 / (1 - Real.exp (-a)) ^ 4) *
      (((2 : ℝ) ^ n) ^ 4 * Real.exp (-(a * (2 : ℝ) ^ n)))
  have ha : 0 < a := by dsimp [a]; positivity
  have hu : Summable u :=
    (summable_forward_derivative_majorant a ha 4).mul_left
      (6 / (1 - Real.exp (-a)) ^ 4)
  change HasDerivAt
    (fun y : ℝ => ∑' n : ℕ, negativeLaplaceForwardTermThird y n)
    (∑' n : ℕ, negativeLaplaceForwardTermFourth s n) s
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermThird y n)
    (g' := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermFourth y n)
    (u := u) (t := Ioi a) (y₀ := s) (y := s)
    hu isOpen_Ioi isPreconnected_Ioi ?_ ?_ ?_ ?_ ?_
  · intro n y hy
    exact negativeLaplaceForwardTermThird_hasDerivAt y (ha.trans hy) n
  · intro n y hy
    exact norm_negativeLaplaceForwardTermFourth_le a y ha hy.le n
  · exact show a < s by dsimp [a]; linarith
  · exact summable_negativeLaplaceForwardTermThird s hs
  · exact show a < s by dsimp [a]; linarith

/-- The first derivative of the forward logarithmic tail on the positive
half-line is its termwise first-derivative series. -/
theorem deriv_negativeLaplaceForwardTail (s : ℝ) (hs : 0 < s) :
    deriv negativeLaplaceForwardTail s =
      negativeLaplaceForwardTailFirst s :=
  (negativeLaplaceForwardTail_hasDerivAt s hs).deriv

/-- The derivative of the first forward-tail series is the second series. -/
theorem deriv_negativeLaplaceForwardTailFirst (s : ℝ) (hs : 0 < s) :
    deriv negativeLaplaceForwardTailFirst s =
      negativeLaplaceForwardTailSecond s :=
  (negativeLaplaceForwardTailFirst_hasDerivAt s hs).deriv

/-- The derivative of the second forward-tail series is the third series. -/
theorem deriv_negativeLaplaceForwardTailSecond (s : ℝ) (hs : 0 < s) :
    deriv negativeLaplaceForwardTailSecond s =
      negativeLaplaceForwardTailThird s :=
  (negativeLaplaceForwardTailSecond_hasDerivAt s hs).deriv

/-- The derivative of the third forward-tail series is the fourth series. -/
theorem deriv_negativeLaplaceForwardTailThird (s : ℝ) (hs : 0 < s) :
    deriv negativeLaplaceForwardTailThird s =
      negativeLaplaceForwardTailFourth s :=
  (negativeLaplaceForwardTailThird_hasDerivAt s hs).deriv

theorem continuousOn_negativeLaplaceForwardTermFourth (n : ℕ) :
    ContinuousOn (fun s : ℝ => negativeLaplaceForwardTermFourth s n) (Ioi 0) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  unfold negativeLaplaceForwardTermFourth
  have hden : 1 - Real.exp (-(s * (2 : ℝ) ^ n)) ≠ 0 :=
    (one_sub_exp_neg_mul_two_pow_pos s hs n).ne'
  have hdenpow : (1 - Real.exp (-(s * (2 : ℝ) ^ n))) ^ 4 ≠ 0 :=
    pow_ne_zero 4 hden
  fun_prop (disch := assumption)

theorem continuousAt_negativeLaplaceForwardTailFourth
    (s : ℝ) (hs : 0 < s) :
    ContinuousAt negativeLaplaceForwardTailFourth s := by
  let a := s / 2
  let b := 3 * s / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hmajor := (summable_forward_derivative_majorant a ha 4).mul_left
    (6 / (1 - Real.exp (-a)) ^ 4)
  have hcont : ContinuousOn negativeLaplaceForwardTailFourth (Icc a b) := by
    change ContinuousOn
      (fun y : ℝ => ∑' n : ℕ, negativeLaplaceForwardTermFourth y n) _
    apply continuousOn_tsum
    · intro n
      exact (continuousOn_negativeLaplaceForwardTermFourth n).mono
        (fun y hy => ha.trans_le hy.1)
    · exact hmajor
    · intro n y hy
      exact norm_negativeLaplaceForwardTermFourth_le a y ha hy.1 n
  exact hcont.continuousAt (Icc_mem_nhds (by dsimp [a]; linarith)
    (by dsimp [b]; linarith))

theorem continuousOn_negativeLaplaceForwardTailFourth :
    ContinuousOn negativeLaplaceForwardTailFourth (Ioi 0) := by
  intro s hs
  exact (continuousAt_negativeLaplaceForwardTailFourth s hs).continuousWithinAt

/-- The forward logarithmic tail is `C⁴` on the positive half-line. -/
theorem contDiffOn_negativeLaplaceForwardTail :
    ContDiffOn ℝ 4 negativeLaplaceForwardTail (Ioi 0) := by
  have hd0 : DifferentiableOn ℝ negativeLaplaceForwardTail (Ioi 0) := by
    intro s hs
    exact (negativeLaplaceForwardTail_hasDerivAt s hs).differentiableAt.differentiableWithinAt
  have hd1 : DifferentiableOn ℝ negativeLaplaceForwardTailFirst (Ioi 0) := by
    intro s hs
    exact (negativeLaplaceForwardTailFirst_hasDerivAt s hs).differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℝ negativeLaplaceForwardTailSecond (Ioi 0) := by
    intro s hs
    exact (negativeLaplaceForwardTailSecond_hasDerivAt s hs).differentiableAt.differentiableWithinAt
  have hd3 : DifferentiableOn ℝ negativeLaplaceForwardTailThird (Ioi 0) := by
    intro s hs
    exact (negativeLaplaceForwardTailThird_hasDerivAt s hs).differentiableAt.differentiableWithinAt
  have h4 : ContDiffOn ℝ 0 negativeLaplaceForwardTailFourth (Ioi 0) :=
    contDiffOn_zero.mpr continuousOn_negativeLaplaceForwardTailFourth
  have h3 : ContDiffOn ℝ 1 negativeLaplaceForwardTailThird (Ioi 0) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨hd3, by simp, ?_⟩
    exact h4.congr fun s hs => deriv_negativeLaplaceForwardTailThird s hs
  have h2 : ContDiffOn ℝ 2 negativeLaplaceForwardTailSecond (Ioi 0) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨hd2, by simp, ?_⟩
    exact h3.congr fun s hs => deriv_negativeLaplaceForwardTailSecond s hs
  have h1 : ContDiffOn ℝ 3 negativeLaplaceForwardTailFirst (Ioi 0) := by
    rw [show (3 : ℕ∞ω) = 2 + 1 by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨hd1, by simp, ?_⟩
    exact h2.congr fun s hs => deriv_negativeLaplaceForwardTailFirst s hs
  rw [show (4 : ℕ∞ω) = 3 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨hd0, by simp, ?_⟩
  exact h1.congr fun s hs => deriv_negativeLaplaceForwardTail s hs

theorem contDiff_fabiusLaplaceMoment_nat
    (F : BoundedFabius) (hF : IsFabius F) (n k : ℕ) :
    ContDiff ℝ n (fabiusLaplaceMoment F k) := by
  induction n generalizing k with
  | zero =>
      change ContDiff ℝ (0 : ℕ∞ω) (fabiusLaplaceMoment F k)
      rw [contDiff_zero]
      have hd : Differentiable ℝ (fabiusLaplaceMoment F k) := fun s =>
        (fabiusLaplaceMoment_hasDerivAt F hF k s).differentiableAt
      exact hd.continuous
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_deriv]
      refine ⟨fun s =>
        (fabiusLaplaceMoment_hasDerivAt F hF k s).differentiableAt, by simp, ?_⟩
      have hderiv : deriv (fabiusLaplaceMoment F k) =
          fun s : ℝ => -fabiusLaplaceMoment F (k + 1) s := by
        funext s
        exact (fabiusLaplaceMoment_hasDerivAt F hF k s).deriv
      rw [hderiv]
      exact (ih (k + 1)).neg

theorem contDiff_negativeLaplaceLog_two_rpow :
    ContDiff ℝ 4 (fun t : ℝ => negativeLaplaceLog ((2 : ℝ) ^ t)) := by
  let F : BoundedFabius := Existence.boundedCandidate
  have hF : IsFabius F := Existence.boundedCandidate_isFabius
  have hM : ContDiff ℝ 4 (fabiusLaplaceMoment F 0) :=
    contDiff_fabiusLaplaceMoment_nat F hF 4 0
  have hpow : ContDiff ℝ 4 (fun t : ℝ => (2 : ℝ) ^ t) := by
    fun_prop (disch := norm_num)
  have hcomp : ContDiff ℝ 4
      (fun t : ℝ => fabiusLaplaceMoment F 0 ((2 : ℝ) ^ t)) :=
    hM.comp hpow
  have hlog : ContDiff ℝ 4
      (fun t : ℝ => Real.log (fabiusLaplaceMoment F 0 ((2 : ℝ) ^ t))) :=
    hcomp.log fun t => (fabiusLaplaceMoment_zero_pos F hF
      (Real.rpow_pos_of_pos (by norm_num) t)).ne'
  have heq : (fun t : ℝ => negativeLaplaceLog ((2 : ℝ) ^ t)) =
      fun t : ℝ => Real.log (fabiusLaplaceMoment F 0 ((2 : ℝ) ^ t)) := by
    funext t
    exact negativeLaplaceLog_eq_log_laplaceMoment F hF
      (Real.rpow_pos_of_pos (by norm_num) t)
  rw [heq]
  exact hlog

theorem contDiff_negativeLaplaceForwardTail_two_rpow :
    ContDiff ℝ 4 (fun t : ℝ => negativeLaplaceForwardTail ((2 : ℝ) ^ t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have htail : ContDiffAt ℝ 4 negativeLaplaceForwardTail ((2 : ℝ) ^ t) :=
    contDiffOn_negativeLaplaceForwardTail.contDiffAt
      (isOpen_Ioi.mem_nhds (Real.rpow_pos_of_pos (by norm_num) t))
  have hpow : ContDiffAt ℝ 4 (fun u : ℝ => (2 : ℝ) ^ u) t := by
    fun_prop (disch := norm_num)
  exact htail.comp t hpow

/-- The exact logarithmic correction is four-times continuously differentiable. -/
theorem contDiff_negativeLaplacePeriodicCorrection :
    ContDiff ℝ 4 negativeLaplacePeriodicCorrection := by
  have heq : negativeLaplacePeriodicCorrection = fun t : ℝ =>
      negativeLaplaceLog ((2 : ℝ) ^ t) +
        Real.log 2 / 2 * (t ^ 2 - t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t) := by
    funext t
    exact negativeLaplacePeriodicCorrection_eq_components t
  rw [heq]
  exact (contDiff_negativeLaplaceLog_two_rpow.add
    (contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_id))).add
      contDiff_negativeLaplaceForwardTail_two_rpow

/-- The zero-mean periodic correction is four-times continuously differentiable. -/
theorem contDiff_negativeLaplacePsi :
    ContDiff ℝ 4 negativeLaplacePsi := by
  unfold negativeLaplacePsi
  exact contDiff_negativeLaplacePeriodicCorrection.sub contDiff_const

theorem negativeLaplacePsi_hasDerivAt (t : ℝ) :
    HasDerivAt negativeLaplacePsi (deriv negativeLaplacePsi t) t :=
  (contDiff_negativeLaplacePsi.differentiable (by norm_num) t).hasDerivAt

theorem contDiff_deriv_negativeLaplacePsi :
    ContDiff ℝ 3 (deriv negativeLaplacePsi) := by
  apply ContDiff.deriv'
  simpa only [show (3 : ℕ∞ω) + 1 = 4 by norm_num] using
    contDiff_negativeLaplacePsi

theorem negativeLaplacePsi_deriv_hasDerivAt (t : ℝ) :
    HasDerivAt (deriv negativeLaplacePsi)
      (deriv (deriv negativeLaplacePsi) t) t :=
  (contDiff_deriv_negativeLaplacePsi.differentiable (by norm_num) t).hasDerivAt

/-- The first derivative of the normalized correction is one-periodic. -/
theorem negativeLaplacePsi_deriv_add_one (t : ℝ) :
    deriv negativeLaplacePsi (t + 1) = deriv negativeLaplacePsi t := by
  have hshift := (negativeLaplacePsi_hasDerivAt (t + 1)).comp t
    ((hasDerivAt_id t).add_const 1)
  have heq : negativeLaplacePsi =ᶠ[𝓝 t]
      negativeLaplacePsi ∘ (fun u : ℝ => id u + 1) :=
    Eventually.of_forall fun u => (negativeLaplacePsi_add_one u).symm
  simpa using (hshift.congr_of_eventuallyEq heq).unique
    (negativeLaplacePsi_hasDerivAt t)

/-- The second derivative of the normalized correction is one-periodic. -/
theorem negativeLaplacePsi_secondDeriv_add_one (t : ℝ) :
    deriv (deriv negativeLaplacePsi) (t + 1) =
      deriv (deriv negativeLaplacePsi) t := by
  have hshift := (negativeLaplacePsi_deriv_hasDerivAt (t + 1)).comp t
    ((hasDerivAt_id t).add_const 1)
  have heq : deriv negativeLaplacePsi =ᶠ[𝓝 t]
      deriv negativeLaplacePsi ∘ (fun u : ℝ => id u + 1) :=
    Eventually.of_forall fun u => (negativeLaplacePsi_deriv_add_one u).symm
  simpa using (hshift.congr_of_eventuallyEq heq).unique
    (negativeLaplacePsi_deriv_hasDerivAt t)

theorem negativeLaplacePsi_deriv_periodic :
    Function.Periodic (deriv negativeLaplacePsi) 1 :=
  negativeLaplacePsi_deriv_add_one

theorem negativeLaplacePsi_secondDeriv_periodic :
    Function.Periodic (deriv (deriv negativeLaplacePsi)) 1 :=
  negativeLaplacePsi_secondDeriv_add_one

theorem continuous_deriv_negativeLaplacePsi :
    Continuous (deriv negativeLaplacePsi) :=
  contDiff_negativeLaplacePsi.continuous_deriv (by norm_num)

theorem continuous_secondDeriv_negativeLaplacePsi :
    Continuous (deriv (deriv negativeLaplacePsi)) :=
  contDiff_deriv_negativeLaplacePsi.continuous_deriv (by norm_num)

theorem isBounded_range_deriv_negativeLaplacePsi :
    Bornology.IsBounded (range (deriv negativeLaplacePsi)) :=
  negativeLaplacePsi_deriv_periodic.isBounded_of_continuous one_ne_zero
    continuous_deriv_negativeLaplacePsi

theorem isBounded_range_secondDeriv_negativeLaplacePsi :
    Bornology.IsBounded (range (deriv (deriv negativeLaplacePsi))) :=
  negativeLaplacePsi_secondDeriv_periodic.isBounded_of_continuous one_ne_zero
    continuous_secondDeriv_negativeLaplacePsi

/-- A global finite bound for the second derivative of the periodic correction. -/
theorem exists_bound_abs_secondDeriv_negativeLaplacePsi :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |deriv (deriv negativeLaplacePsi) t| ≤ C := by
  rcases (Metric.isBounded_iff_subset_closedBall 0).mp
      isBounded_range_secondDeriv_negativeLaplacePsi with ⟨C, hC⟩
  have hzero := hC (mem_range_self (0 : ℝ))
  have hC0 : 0 ≤ C := by
    have hnorm : |deriv (deriv negativeLaplacePsi) 0| ≤ C := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hzero
    exact (abs_nonneg _).trans hnorm
  refine ⟨C, hC0, ?_⟩
  intro t
  simpa [Metric.mem_closedBall, Real.dist_eq] using hC (mem_range_self t)

/-- A global quadratic Taylor bound for the zero-mean periodic correction. -/
theorem exists_negativeLaplacePsi_first_order_remainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h : ℝ,
      |negativeLaplacePsi (x + h) - negativeLaplacePsi x -
          deriv negativeLaplacePsi x * h| ≤ C * h ^ 2 := by
  rcases exists_bound_abs_secondDeriv_negativeLaplacePsi with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro x h
  by_cases hh : h = 0
  · subst h
    simp
  have hx : x ≠ x + h := by
    intro heq
    apply hh
    linarith
  have hsmooth : ContDiffOn ℝ (1 + 1) negativeLaplacePsi (uIcc x (x + h)) :=
    contDiff_negativeLaplacePsi.contDiffOn.of_le (by norm_num)
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv hx hsmooth
  have hu : UniqueDiffOn ℝ (uIcc x (x + h)) := uniqueDiffOn_Icc (by grind)
  have hxmem : x ∈ uIcc x (x + h) := left_mem_uIcc
  have hfirst :
      iteratedDerivWithin 1 negativeLaplacePsi (uIcc x (x + h)) x =
        deriv negativeLaplacePsi x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (contDiff_negativeLaplacePsi.contDiffAt.of_le (by norm_num)) hxmem]
    simp [iteratedDeriv_succ]
  have htaylor :
      taylorWithinEval negativeLaplacePsi 1 (uIcc x (x + h)) x (x + h) =
        negativeLaplacePsi x + deriv negativeLaplacePsi x * h := by
    rw [show (1 : ℕ) = 0 + 1 by norm_num, taylorWithinEval_succ,
      taylor_within_zero_eval, hfirst]
    simp
    ring
  have hsecond :
      iteratedDeriv 2 negativeLaplacePsi y =
        deriv (deriv negativeLaplacePsi) y := by
    simp [iteratedDeriv_succ]
  rw [htaylor, hsecond, show x + h - x = h by ring] at hrem
  have habs := congrArg abs hrem
  rw [abs_div, abs_mul, abs_pow] at habs
  norm_num at habs
  rw [show negativeLaplacePsi (x + h) - negativeLaplacePsi x -
      deriv negativeLaplacePsi x * h =
        negativeLaplacePsi (x + h) -
          (negativeLaplacePsi x + deriv negativeLaplacePsi x * h) by ring,
    habs]
  have hbound : |deriv (deriv negativeLaplacePsi) y| ≤ C := hC y
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  calc
    |deriv (deriv negativeLaplacePsi) y| * h ^ 2 / 2 ≤
        C * h ^ 2 / 2 := by gcongr
    _ ≤ C * h ^ 2 := by
      nlinarith

end Fabius
