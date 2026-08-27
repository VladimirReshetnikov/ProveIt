import FabiusFunction.Differential
import FabiusFunction.DyadicAnalytic
import FabiusFunction.MomentPowerSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Analytic moment identities for the Fabius function

This module proves the integral interpretations of the exact moment sequences,
their inverse-power specializations, and the generating-function dilation
identity from Proposition 2 of *Arithmetic of the Fabius function*.  The
source-facing positive-index half-moment identity is complemented by a
totalized all-index form whose normalized zeroth term is one.  A generic
summation lemma also records that deleting identically zero odd terms
preserves the sum of a convergent series.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff Interval
open Set Finset MeasureTheory

namespace Fabius

private lemma rvachev_continuous (F : BoundedFabius) (hF : IsFabius F) :
    Continuous (rvachevUp F) :=
  (rvachev_contDiff F hF).continuous

/-- Every monomial multiple of Rvachev's function is continuous. -/
theorem pow_mul_rvachev_continuous (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) : Continuous (fun x : ℝ => x ^ m * rvachevUp F x) :=
  (continuous_id.pow m).mul (rvachev_continuous F hF)

private lemma pow_mul_rvachev_intervalIntegrable
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ m * rvachevUp F x) volume a b :=
  (pow_mul_rvachev_continuous F hF m).intervalIntegrable a b

private lemma integral_eq_interval_of_support_subset_rvachevUp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : BoundedFabius) (hF : IsFabius F) (f : ℝ → E)
    (hf : Function.support f ⊆ Function.support (rvachevUp F)) :
    (∫ x : ℝ, f x) = ∫ x in (-1 : ℝ)..1, f x :=
  (intervalIntegral.integral_eq_integral_of_support_subset
    (hf.trans ((support_rvachev_subset_Ioo F hF).trans
      Ioo_subset_Ioc_self))).symm

private lemma integral_pow_mul_rvachev_symm
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ m * rvachevUp F x) =
      (((-1 : ℝ) ^ m) + 1) *
        ∫ x in (0 : ℝ)..1, x ^ m * rvachevUp F x := by
  let f : ℝ → ℝ := fun x => x ^ m * rvachevUp F x
  have hneg := intervalIntegral.integral_comp_neg
    (f := f) (a := (0 : ℝ)) (b := 1)
  have hreflect : (∫ x in (0 : ℝ)..1, f (-x)) =
      (-1 : ℝ) ^ m * ∫ x in (0 : ℝ)..1, f x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp [f]
    rw [rvachev_even F hF x]
    rw [neg_pow]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (pow_mul_rvachev_intervalIntegrable F hF m (-1) 0)
    (pow_mul_rvachev_intervalIntegrable F hF m 0 1)
  change (∫ x in (-1 : ℝ)..1, f x) = _
  change (∫ x in (-1 : ℝ)..0, f x) +
      (∫ x in (0 : ℝ)..1, f x) =
        (∫ x in (-1 : ℝ)..1, f x) at hsplit
  have hneg' : (∫ x in (0 : ℝ)..1, f (-x)) =
      ∫ x in (-1 : ℝ)..0, f x := by
    convert hneg using 1
    norm_num
  rw [← hneg', hreflect] at hsplit
  linarith

private lemma integral_pow_mul_rvachev_eq_interval
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    (∫ x : ℝ, x ^ m * rvachevUp F x) =
      ∫ x in (-1 : ℝ)..1, x ^ m * rvachevUp F x := by
  apply integral_eq_interval_of_support_subset_rvachevUp F hF
  intro x hx
  change rvachevUp F x ≠ 0
  intro hzero
  exact hx (by simp [hzero])

/-- Rvachev's compactly supported function has total mass one. -/
theorem integral_rvachev_eq_one (F : BoundedFabius) (hF : IsFabius F) :
    (∫ x : ℝ, rvachevUp F x) = 1 := by
  have hderiv : ∀ x ∈ [[(0 : ℝ), 1]],
      HasDerivAt (rvachevUp F) (-2 * rvachevUp F (2 * x - 1)) x := by
    intro x hx
    have hxmem : x ∈ Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hfar : rvachevUp F (2 * x + 1) = 0 :=
      rvachevUp_eq_zero_of_one_le F hF (by linarith [hxmem.1])
    convert rvachev_hasDerivAt F hF x using 1
    rw [hfar]
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => -2 * rvachevUp F (2 * x - 1)) volume 0 1 := by
    exact (continuous_const.mul ((rvachev_continuous F hF).comp
      (continuous_const.mul continuous_id |>.sub continuous_const))).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsub := intervalIntegral.mul_integral_comp_mul_sub
    (f := rvachevUp F) (a := (0 : ℝ)) (b := 1) 2 1
  have hends : rvachevUp F 1 - rvachevUp F 0 = -1 := by
    rw [rvachevUp_eq_zero_of_one_le F hF le_rfl, rvachevUp_zero F hF]
    norm_num
  rw [intervalIntegral.integral_const_mul] at hftc
  rw [hends] at hftc
  have hsub' : 2 * (∫ x in (0 : ℝ)..1, rvachevUp F (2 * x - 1)) =
      ∫ x in (-1 : ℝ)..1, rvachevUp F x := by
    convert hsub using 1
    norm_num
  have hinter : (∫ x in (-1 : ℝ)..1, rvachevUp F x) = 1 := by
    linarith [hsub']
  calc
    (∫ x : ℝ, rvachevUp F x) =
        ∫ x in (-1 : ℝ)..1, rvachevUp F x := by
      simpa using integral_pow_mul_rvachev_eq_interval F hF 0
    _ = 1 := hinter

private lemma scaled_half_moment_identity
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) (hr : 1 ≤ r) :
    (2 : ℝ) ^ r * (r : ℝ) *
        (∫ x in (0 : ℝ)..1, x ^ (r - 1) * rvachevUp F x) =
      ∫ x in (-1 : ℝ)..1, (x + 1) ^ r * rvachevUp F x := by
  let u : ℝ → ℝ := fun x => x ^ r
  let u' : ℝ → ℝ := fun x => (r : ℝ) * x ^ (r - 1)
  let v' : ℝ → ℝ := fun x => -2 * rvachevUp F (2 * x - 1)
  have hu : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt u (u' x) x := by
    intro x _hx
    exact hasDerivAt_pow r x
  have hv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt (rvachevUp F) (v' x) x := by
    intro x hx
    have hxmem : x ∈ Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hfar : rvachevUp F (2 * x + 1) = 0 :=
      rvachevUp_eq_zero_of_one_le F hF (by linarith [hxmem.1])
    dsimp [v']
    convert rvachev_hasDerivAt F hF x using 1
    rw [hfar]
    ring
  have hu_int : IntervalIntegrable u' volume 0 1 := by
    exact (continuous_const.mul (continuous_id.pow (r - 1))).intervalIntegrable 0 1
  have hv_int : IntervalIntegrable v' volume 0 1 := by
    exact (continuous_const.mul ((rvachev_continuous F hF).comp
      (continuous_const.mul continuous_id |>.sub continuous_const))).intervalIntegrable 0 1
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu_int hv_int
  have hu_zero : u 0 = 0 := by simp [u, Nat.ne_zero_of_lt hr]
  have hv_zero : rvachevUp F 1 = 0 :=
    rvachevUp_eq_zero_of_one_le F hF le_rfl
  have hbyParts : (r : ℝ) *
      (∫ x in (0 : ℝ)..1, x ^ (r - 1) * rvachevUp F x) =
        2 * ∫ x in (0 : ℝ)..1, x ^ r * rvachevUp F (2 * x - 1) := by
    dsimp [u, u', v'] at hparts
    have hleft : (∫ x in (0 : ℝ)..1,
        x ^ r * (-2 * rvachevUp F (2 * x - 1))) =
        -2 * ∫ x in (0 : ℝ)..1, x ^ r * rvachevUp F (2 * x - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    have hright : (∫ x in (0 : ℝ)..1,
        (r : ℝ) * x ^ (r - 1) * rvachevUp F x) =
        (r : ℝ) * ∫ x in (0 : ℝ)..1, x ^ (r - 1) * rvachevUp F x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    rw [hleft, hright] at hparts
    have hr0 : r ≠ 0 := by omega
    simp only [hv_zero, one_pow, mul_zero, zero_pow hr0, zero_mul, sub_zero,
      zero_sub] at hparts
    linarith
  let g : ℝ → ℝ := fun t => ((t + 1) / 2) ^ r * rvachevUp F t
  have hsub0 := intervalIntegral.mul_integral_comp_mul_sub
    (f := g) (a := (0 : ℝ)) (b := 1) 2 1
  have hsub : 2 * (∫ x in (0 : ℝ)..1,
      x ^ r * rvachevUp F (2 * x - 1)) =
      ∫ t in (-1 : ℝ)..1, g t := by
    have hcongr : (∫ x in (0 : ℝ)..1, g (2 * x - 1)) =
        ∫ x in (0 : ℝ)..1, x ^ r * rvachevUp F (2 * x - 1) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp [g]
      congr 2
      ring
    rw [hcongr] at hsub0
    convert hsub0 using 1
    all_goals norm_num
  have hscale : (2 : ℝ) ^ r * (∫ t in (-1 : ℝ)..1, g t) =
      ∫ t in (-1 : ℝ)..1, (t + 1) ^ r * rvachevUp F t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [g]
    rw [div_pow]
    field_simp
  rw [mul_assoc, hbyParts, hsub]
  exact hscale

private lemma integral_add_one_pow_mul_rvachev
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    (∫ x in (-1 : ℝ)..1, (x + 1) ^ r * rvachevUp F x) =
      ∑ j ∈ range (r + 1), (Nat.choose r j : ℝ) *
        (∫ x in (-1 : ℝ)..1, x ^ j * rvachevUp F x) := by
  have hpoint : ∀ x : ℝ,
      (x + 1) ^ r * rvachevUp F x =
        ∑ j ∈ range (r + 1),
          ((Nat.choose r j : ℝ) * (x ^ j * rvachevUp F x)) := by
    intro x
    rw [add_pow]
    simp only [one_pow, mul_one]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [intervalIntegral.integral_congr (fun x _hx => hpoint x)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_const_mul]
  · intro j hj
    exact (continuous_const.mul (pow_mul_rvachev_continuous F hF j)).intervalIntegrable
      (-1) 1

private lemma integral_add_one_odd_pow_mul_rvachev
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (x + 1) ^ (2 * n + 1) * rvachevUp F x) =
      ∑ k ∈ range (n + 1), (Nat.choose (2 * n + 1) (2 * k) : ℝ) *
        (∫ x in (-1 : ℝ)..1, x ^ (2 * k) * rvachevUp F x) := by
  rw [integral_add_one_pow_mul_rvachev F hF]
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
  rw [sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hodd := integral_pow_mul_rvachev_symm F hF (2 * k + 1)
  have hodd0 : (∫ x in (-1 : ℝ)..1,
      x ^ (2 * k + 1) * rvachevUp F x) = 0 := by
    simpa [pow_succ] using hodd
  rw [hodd0]
  ring

/-- Every odd moment over the symmetric support interval vanishes. -/
theorem intervalIntegral_odd_pow_mul_rvachev_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ (2 * k + 1) * rvachevUp F x) = 0 := by
  have h := integral_pow_mul_rvachev_symm F hF (2 * k + 1)
  simpa [pow_succ] using h

private lemma binomial_integral_sum_eq_even
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (∑ j ∈ range (n + 1), (Nat.choose n j : ℝ) *
        (∫ x in (-1 : ℝ)..1, x ^ j * rvachevUp F x)) =
      ∑ k ∈ range (n / 2 + 1), (Nat.choose n (2 * k) : ℝ) *
        (∫ x in (-1 : ℝ)..1, x ^ (2 * k) * rvachevUp F x) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    have hdiv : 2 * m / 2 + 1 = m + 1 := by omega
    rw [hdiv]
    rw [show 2 * m + 1 = 2 * m + 1 by rfl, sum_range_succ]
    rw [sum_range_two_mul]
    rw [sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral_odd_pow_mul_rvachev_eq_zero F hF]
      ring
  · subst n
    have hdiv : (2 * m + 1) / 2 + 1 = m + 1 := by omega
    rw [hdiv]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
    rw [sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral_odd_pow_mul_rvachev_eq_zero F hF]
    ring

private lemma momentIntegral_recurrence_all
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n) * momentIntegral F n =
      ∑ k ∈ range (n + 1), (Nat.choose (2 * n + 1) (2 * k) : ℝ) *
        momentIntegral F k := by
  have hscaled := scaled_half_moment_identity F hF (2 * n + 1) (by omega)
  have hsym0 := integral_pow_mul_rvachev_symm F hF (2 * n)
  have hsym : (∫ x in (-1 : ℝ)..1, x ^ (2 * n) * rvachevUp F x) =
      2 * ∫ x in (0 : ℝ)..1, x ^ (2 * n) * rvachevUp F x := by
    convert hsym0 using 1
    norm_num [pow_mul]
  have hloc : momentIntegral F n =
      ∫ x in (-1 : ℝ)..1, x ^ (2 * n) * rvachevUp F x := by
    exact integral_pow_mul_rvachev_eq_interval F hF (2 * n)
  have hleft : (2 : ℝ) ^ (2 * n + 1) * ((2 * n + 1 : ℕ) : ℝ) *
      (∫ x in (0 : ℝ)..1, x ^ (2 * n + 1 - 1) * rvachevUp F x) =
      ((2 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n) *
        momentIntegral F n := by
    rw [show 2 * n + 1 - 1 = 2 * n by omega]
    rw [hloc, hsym, pow_succ]
    ring
  have hrhs : (∫ x in (-1 : ℝ)..1,
      (x + 1) ^ (2 * n + 1) * rvachevUp F x) =
      ∑ k ∈ range (n + 1), (Nat.choose (2 * n + 1) (2 * k) : ℝ) *
        momentIntegral F k := by
    rw [integral_add_one_odd_pow_mul_rvachev F hF n]
    apply Finset.sum_congr rfl
    intro k hk
    have hlock := integral_pow_mul_rvachev_eq_interval F hF (2 * k)
    rw [← hlock]
    rfl
  rw [← hleft]
  exact hscaled.trans hrhs

private lemma momentIntegral_original_recurrence
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (2 * n) - 1) *
        momentIntegral F n =
      ∑ k ∈ range n, (Nat.choose (2 * n + 1) (2 * k) : ℝ) *
        momentIntegral F k := by
  have h := momentIntegral_recurrence_all F hF n
  rw [sum_range_succ] at h
  have hchoose : (2 * n + 1).choose (2 * n) = 2 * n + 1 := by
    exact Nat.choose_succ_self_right (2 * n)
  rw [hchoose] at h
  push_cast at h
  push_cast
  linear_combination h

/-- The executable rational moment is exactly its analytic integral model:
`(moment n : ℝ) = momentIntegral F n`, the full-line moment of order `2 * n`
of Rvachev's function. -/
theorem moment_eq_integral_formula (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (moment n : ℝ) = momentIntegral F n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [moment_zero]
          norm_num [momentIntegral, integral_rvachev_eq_one F hF]
      | succ n =>
          rw [moment_succ]
          rw [Fin.sum_univ_eq_sum_range
            (fun k => (Nat.choose (2 * (n + 1) + 1) (2 * k) : ℚ) * moment k)
            (n + 1)]
          push_cast
          have hrec := momentIntegral_original_recurrence F hF (n + 1)
          have hden : (((2 * (n + 1) + 1 : ℕ) : ℝ) *
              ((2 : ℝ) ^ (2 * (n + 1)) - 1)) ≠ 0 := by
            apply mul_ne_zero
            · positivity
            · exact sub_ne_zero.mpr (ne_of_gt
                (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega)))
          have hsolve : momentIntegral F (n + 1) =
              (∑ k ∈ range (n + 1),
                (Nat.choose (2 * (n + 1) + 1) (2 * k) : ℝ) *
                  momentIntegral F k) /
                (((2 * (n + 1) + 1 : ℕ) : ℝ) *
                  ((2 : ℝ) ^ (2 * (n + 1)) - 1)) := by
            apply (eq_div_iff hden).2
            simpa [mul_comm] using hrec
          rw [hsolve]
          push_cast
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k (by simp only [Finset.mem_range] at hk; omega)]

/-- The full-line even moments of Rvachev's function are the executable
rational moment sequence. -/
theorem integral_even_pow_mul_rvachev_eq_moment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) * rvachevUp F x) = (moment n : ℝ) := by
  simpa only [momentIntegral] using (moment_eq_integral_formula F hF n).symm

/-- Every full-line odd moment of Rvachev's function vanishes. -/
theorem integral_odd_pow_mul_rvachev_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n + 1) * rvachevUp F x) = 0 := by
  calc
    (∫ x : ℝ, x ^ (2 * n + 1) * rvachevUp F x) =
        ∫ x in (-1 : ℝ)..1, x ^ (2 * n + 1) * rvachevUp F x :=
      integral_pow_mul_rvachev_eq_interval F hF (2 * n + 1)
    _ = 0 := intervalIntegral_odd_pow_mul_rvachev_eq_zero F hF n

private lemma halfMomentIntegral_eq_evenMoment_sum
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    halfMomentIntegral F n =
      (∑ k ∈ range (n / 2 + 1), (Nat.choose n (2 * k) : ℝ) *
        momentIntegral F k) / (2 : ℝ) ^ n := by
  cases n with
  | zero => omega
  | succ m =>
      have hscaled := scaled_half_moment_identity F hF (m + 1) (by omega)
      have hrhs : (∫ x in (-1 : ℝ)..1,
          (x + 1) ^ (m + 1) * rvachevUp F x) =
          ∑ k ∈ range ((m + 1) / 2 + 1),
            (Nat.choose (m + 1) (2 * k) : ℝ) * momentIntegral F k := by
        rw [integral_add_one_pow_mul_rvachev F hF]
        rw [binomial_integral_sum_eq_even F hF]
        apply Finset.sum_congr rfl
        intro k hk
        have hloc := integral_pow_mul_rvachev_eq_interval F hF (2 * k)
        rw [← hloc]
        rfl
      have hmain := hscaled.trans hrhs
      simp only [halfMomentIntegral_succ]
      apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmain

/-- The rational half-moment sequence agrees with its normalized integral
model at every index.  At `n = 0` both sides are defined to be `1`; successor
indices are the integral identity proved from the even moments. -/
theorem halfMoment_eq_integral_formula_all
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (halfMoment n : ℝ) = halfMomentIntegral F n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [halfMoment_eq_evenMomentSum]
      push_cast
      rw [halfMomentIntegral_eq_evenMoment_sum F hF (n + 1) (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [moment_eq_integral_formula F hF k]

/-- Positive-index compatibility form of
`halfMoment_eq_integral_formula_all`, retaining the paper's original
positivity hypothesis and public binder order. -/
theorem halfMoment_eq_integral_formula (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    (halfMoment n : ℝ) = halfMomentIntegral F n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact halfMoment_eq_integral_formula_all F hF (1 + m)

/-- Exact inverse-dyadic formula for every rational half moment:
`(halfMoment n : ℝ) = n.factorial * 2 ^ n.choose 2 *
fabiusReal F (((2 : ℝ) ^ n)⁻¹)`. -/
theorem halfMoment_eq_fabius_formula (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (halfMoment n : ℝ) =
      n.factorial * 2 ^ n.choose 2 * fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  have h := fabiusDyadic_cast F hF n 1 Nat.one_le_two_pow
  change (fabiusAtInverseTwoPow n : ℝ) = _ at h
  rw [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue] at h
  push_cast at h
  have hden : ((n.factorial : ℝ) * (2 : ℝ) ^ n.choose 2) ≠ 0 := by
    positivity
  rw [div_eq_iff hden] at h
  simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using h

private lemma rvachev_one_sub_inverse_pow_eq_fabius
    (F : BoundedFabius) (n : ℕ) (hn : 1 ≤ n) :
    rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹) = fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, pow_one]
    have hm : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hinv : ((2 : ℝ) ^ n)⁻¹ < 1 := by
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    rw [inv_lt_one₀ hp]
    linarith
  rw [rvachevUp, if_neg (not_le.mpr (by linarith : 0 < 1 - ((2 : ℝ) ^ n)⁻¹))]
  congr 1
  ring

/-- For `1 ≤ n`, the weighted half-line moment is the inverse-dyadic value
`(n : ℝ) * ∫ t in 0..1, t ^ (n - 1) * rvachevUp F t =
n.factorial * 2 ^ n.choose 2 *
rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹)`. -/
theorem halfIntegral_eq_rvachev_dyadic_formula
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * ∫ t in (0 : ℝ)..1, t ^ (n - 1) * rvachevUp F t =
      n.factorial * 2 ^ n.choose 2 *
        rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹) := by
  have hint : halfMomentIntegral F n =
      (n : ℝ) * ∫ t in (0 : ℝ)..1, t ^ (n - 1) * rvachevUp F t := by
    cases n with
    | zero => omega
    | succ m => rfl
  calc
    (n : ℝ) * ∫ t in (0 : ℝ)..1, t ^ (n - 1) * rvachevUp F t =
        halfMomentIntegral F n := hint.symm
    _ = (halfMoment n : ℝ) := (halfMoment_eq_integral_formula_all F hF n).symm
    _ = n.factorial * 2 ^ n.choose 2 *
        fabiusReal F (((2 : ℝ) ^ n)⁻¹) := halfMoment_eq_fabius_formula F hF n
    _ = n.factorial * 2 ^ n.choose 2 *
        rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹) := by
      rw [rvachev_one_sub_inverse_pow_eq_fabius F n hn]

/-- The half-line even moment is both half of the full moment and an exact
inverse-dyadic Rvachev value:
`(moment n : ℝ) / 2 = ∫ t in 0..1, t ^ (2 * n) * rvachevUp F t`, and
this integral is `(2 * n).factorial * 2 ^ (2 * n + 1).choose 2 *
rvachevUp F (1 - ((2 : ℝ) ^ (2 * n + 1))⁻¹)`. -/
theorem moment_halfIntegral_eq_rvachev_dyadic_formula
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (moment n : ℝ) / 2 =
        ∫ t in (0 : ℝ)..1, t ^ (2 * n) * rvachevUp F t ∧
    (∫ t in (0 : ℝ)..1, t ^ (2 * n) * rvachevUp F t) =
      (Nat.factorial (2 * n) : ℝ) * 2 ^ (2 * n + 1).choose 2 *
        rvachevUp F (1 - ((2 : ℝ) ^ (2 * n + 1))⁻¹) := by
  constructor
  · rw [moment_eq_integral_formula F hF n]
    change (∫ x : ℝ, x ^ (2 * n) * rvachevUp F x) / 2 = _
    have hloc := integral_pow_mul_rvachev_eq_interval F hF (2 * n)
    have hsym0 := integral_pow_mul_rvachev_symm F hF (2 * n)
    have hsym : (∫ x in (-1 : ℝ)..1, x ^ (2 * n) * rvachevUp F x) =
        2 * ∫ x in (0 : ℝ)..1, x ^ (2 * n) * rvachevUp F x := by
      convert hsym0 using 1
      norm_num [pow_mul]
    rw [hloc, hsym]
    ring
  · have h := halfIntegral_eq_rvachev_dyadic_formula F hF (2 * n + 1) (by omega)
    rw [show 2 * n + 1 - 1 = 2 * n by omega] at h
    rw [Nat.factorial_succ] at h
    push_cast at h
    have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
    nlinarith

private noncomputable def rvachevLaplace (F : BoundedFabius) (z : ℂ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, (rvachevUp F t : ℂ) * Complex.exp (z * t)

private lemma rvachev_complex_continuous
    (F : BoundedFabius) (hF : IsFabius F) :
    Continuous (fun t : ℝ => (rvachevUp F t : ℂ)) :=
  Complex.continuous_ofReal.comp (rvachev_continuous F hF)

private lemma complex_exp_mul_continuous (z : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (z * t)) := by
  fun_prop

private lemma rvachev_complex_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (rvachevUp F t : ℂ))
      (2 * ((rvachevUp F (2 * x + 1) : ℂ) -
        (rvachevUp F (2 * x - 1) : ℂ))) x := by
  simpa using (rvachev_hasDerivAt F hF x).ofReal_comp

private lemma complex_exp_mul_hasDerivAt (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (z * t))
      (Complex.exp (z * x) * z) x := by
  have hlin : HasDerivAt (fun t : ℝ => z * t) z x := by
    simpa only [mul_one] using!
      ((hasDerivAt_id (x : ℂ)).const_mul z).comp_ofReal
  exact hlin.cexp

private lemma shifted_laplace_plus
    (F : BoundedFabius) (z : ℂ) :
    2 * (∫ t in (0 : ℝ)..1,
      (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t)) =
      Complex.exp (z / 2) * rvachevLaplace F (z / 2) := by
  let g : ℝ → ℂ := fun y =>
    (rvachevUp F y : ℂ) * Complex.exp (z * ((y + 1) / 2))
  have hsub0 := intervalIntegral.smul_integral_comp_mul_sub
    (f := g) (a := (0 : ℝ)) (b := 1) 2 1
  have hsub : 2 * (∫ t in (0 : ℝ)..1,
      (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t)) =
      ∫ y in (-1 : ℝ)..1, g y := by
    have hcongr : (∫ t in (0 : ℝ)..1, g (2 * t - 1)) =
        ∫ t in (0 : ℝ)..1,
          (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp [g]
      congr 2
      congr 1
      push_cast
      ring
    rw [hcongr] at hsub0
    convert hsub0 using 1
    all_goals norm_num
  rw [hsub, rvachevLaplace, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp [g]
  have hz : z * (((y : ℂ) + 1) / 2) = z / 2 + (z / 2) * y := by ring
  rw [hz, Complex.exp_add]
  ring

private lemma complexGeneratingFunction_eq_exp_mul_laplace
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z =
      Complex.exp (z / 2) * rvachevLaplace F (z / 2) := by
  let uc : ℝ → ℂ := fun t => (rvachevUp F t : ℂ)
  let e : ℝ → ℂ := fun t => Complex.exp (z * t)
  let u' : ℝ → ℂ := fun t => -2 * (rvachevUp F (2 * t - 1) : ℂ)
  let e' : ℝ → ℂ := fun t => Complex.exp (z * t) * z
  have hu : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt uc (u' x) x := by
    intro x hx
    have hxmem : x ∈ Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hfar : rvachevUp F (2 * x + 1) = 0 :=
      rvachevUp_eq_zero_of_one_le F hF (by linarith [hxmem.1])
    dsimp [uc, u']
    convert rvachev_complex_hasDerivAt F hF x using 1
    rw [hfar]
    norm_num
  have he : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt e (e' x) x := by
    intro x _hx
    exact complex_exp_mul_hasDerivAt z x
  have hu'_int : IntervalIntegrable u' volume 0 1 := by
    exact (continuous_const.mul ((rvachev_complex_continuous F hF).comp
      (continuous_const.mul continuous_id |>.sub continuous_const))).intervalIntegrable 0 1
  have he'_int : IntervalIntegrable e' volume 0 1 := by
    exact ((complex_exp_mul_continuous z).mul continuous_const).intervalIntegrable 0 1
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub hu he hu'_int he'_int
  have hfirst_int : IntervalIntegrable (fun t => u' t * e t) volume 0 1 := by
    exact ((continuous_const.mul ((rvachev_complex_continuous F hF).comp
      (continuous_const.mul continuous_id |>.sub continuous_const))).mul
        (complex_exp_mul_continuous z)).intervalIntegrable 0 1
  have hsecond_int : IntervalIntegrable (fun t => uc t * e' t) volume 0 1 := by
    exact ((rvachev_complex_continuous F hF).mul
      ((complex_exp_mul_continuous z).mul continuous_const)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hfirst_int hsecond_int] at hparts
  have hfirst : (∫ t in (0 : ℝ)..1, u' t * e t) =
      -2 * ∫ t in (0 : ℝ)..1,
        (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [u', e]
    ring
  have hsecond : (∫ t in (0 : ℝ)..1, uc t * e' t) =
      (∫ t in (0 : ℝ)..1,
        (rvachevUp F t : ℂ) * Complex.exp (z * t)) * z := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [uc, e']
    ring
  rw [hfirst, hsecond] at hparts
  have hboundary : uc 1 * e 1 - uc 0 * e 0 = -1 := by
    dsimp [uc, e]
    rw [rvachevUp_eq_zero_of_one_le F hF le_rfl, rvachevUp_zero F hF]
    norm_num
  rw [hboundary] at hparts
  have hgen : complexGeneratingFunction F z =
      2 * ∫ t in (0 : ℝ)..1,
        (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t) := by
    rw [complexGeneratingFunction]
    linear_combination hparts
  rw [hgen, shifted_laplace_plus F z]

private lemma shifted_laplace_minus
    (F : BoundedFabius) (z : ℂ) :
    2 * (∫ t in (-1 : ℝ)..0,
      (rvachevUp F (2 * t + 1) : ℂ) * Complex.exp (z * t)) =
      Complex.exp (-z / 2) * rvachevLaplace F (z / 2) := by
  let g : ℝ → ℂ := fun y =>
    (rvachevUp F y : ℂ) * Complex.exp (z * ((y - 1) / 2))
  have hsub0 := intervalIntegral.smul_integral_comp_mul_add
    (f := g) (a := (-1 : ℝ)) (b := 0) 2 1
  have hsub : 2 * (∫ t in (-1 : ℝ)..0,
      (rvachevUp F (2 * t + 1) : ℂ) * Complex.exp (z * t)) =
      ∫ y in (-1 : ℝ)..1, g y := by
    have hcongr : (∫ t in (-1 : ℝ)..0, g (2 * t + 1)) =
        ∫ t in (-1 : ℝ)..0,
          (rvachevUp F (2 * t + 1) : ℂ) * Complex.exp (z * t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp [g]
      congr 2
      congr 1
      push_cast
      ring
    rw [hcongr] at hsub0
    convert hsub0 using 1
    all_goals norm_num
  rw [hsub, rvachevLaplace, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp [g]
  have hz : z * (((y : ℂ) - 1) / 2) = -z / 2 + (z / 2) * y := by ring
  rw [hz, Complex.exp_add]
  ring

private lemma rvachevLaplace_scaling
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    z * rvachevLaplace F z =
      (Complex.exp (z / 2) - Complex.exp (-z / 2)) *
        rvachevLaplace F (z / 2) := by
  let uc : ℝ → ℂ := fun t => (rvachevUp F t : ℂ)
  let e : ℝ → ℂ := fun t => Complex.exp (z * t)
  let u' : ℝ → ℂ := fun t =>
    2 * ((rvachevUp F (2 * t + 1) : ℂ) -
      (rvachevUp F (2 * t - 1) : ℂ))
  let e' : ℝ → ℂ := fun t => Complex.exp (z * t) * z
  have hu : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt uc (u' x) x := by
    intro x _hx
    exact rvachev_complex_hasDerivAt F hF x
  have he : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt e (e' x) x := by
    intro x _hx
    exact complex_exp_mul_hasDerivAt z x
  have hu'_cont : Continuous u' := by
    exact continuous_const.mul
      (((rvachev_complex_continuous F hF).comp
        (continuous_const.mul continuous_id |>.add continuous_const)).sub
       ((rvachev_complex_continuous F hF).comp
        (continuous_const.mul continuous_id |>.sub continuous_const)))
  have he'_cont : Continuous e' :=
    (complex_exp_mul_continuous z).mul continuous_const
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub hu he
    (hu'_cont.intervalIntegrable (-1) 1) (he'_cont.intervalIntegrable (-1) 1)
  have hfirst_int : IntervalIntegrable (fun t => u' t * e t) volume (-1) 1 :=
    (hu'_cont.mul (complex_exp_mul_continuous z)).intervalIntegrable (-1) 1
  have hsecond_int : IntervalIntegrable (fun t => uc t * e' t) volume (-1) 1 :=
    ((rvachev_complex_continuous F hF).mul he'_cont).intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_add hfirst_int hsecond_int] at hparts
  have hsecond : (∫ t in (-1 : ℝ)..1, uc t * e' t) =
      rvachevLaplace F z * z := by
    rw [rvachevLaplace, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [uc, e']
    ring
  rw [hsecond] at hparts
  have hboundary : uc 1 * e 1 - uc (-1) * e (-1) = 0 := by
    dsimp [uc, e]
    rw [rvachevUp_eq_zero_of_one_le F hF le_rfl,
      rvachevUp_eq_zero_of_le_neg_one F hF le_rfl]
    norm_num
  rw [hboundary] at hparts
  have hderiv : (∫ t in (-1 : ℝ)..1, u' t * e t) =
      (Complex.exp (-z / 2) - Complex.exp (z / 2)) *
        rvachevLaplace F (z / 2) := by
    have hint_neg : IntervalIntegrable (fun t => u' t * e t) volume (-1) 0 :=
      (hu'_cont.mul (complex_exp_mul_continuous z)).intervalIntegrable (-1) 0
    have hint_pos : IntervalIntegrable (fun t => u' t * e t) volume 0 1 :=
      (hu'_cont.mul (complex_exp_mul_continuous z)).intervalIntegrable 0 1
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint_neg hint_pos
    have hneg : (∫ t in (-1 : ℝ)..0, u' t * e t) =
        2 * ∫ t in (-1 : ℝ)..0,
          (rvachevUp F (2 * t + 1) : ℂ) * Complex.exp (z * t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      have htmem : t ∈ Icc (-1 : ℝ) 0 := by
        simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using ht
      have hfar : rvachevUp F (2 * t - 1) = 0 :=
        rvachevUp_eq_zero_of_le_neg_one F hF (by linarith [htmem.2])
      dsimp [u', e]
      rw [hfar]
      norm_num
      ring
    have hpos : (∫ t in (0 : ℝ)..1, u' t * e t) =
        -2 * ∫ t in (0 : ℝ)..1,
          (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      have htmem : t ∈ Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hfar : rvachevUp F (2 * t + 1) = 0 :=
        rvachevUp_eq_zero_of_one_le F hF (by linarith [htmem.1])
      dsimp [u', e]
      rw [hfar]
      norm_num
      ring
    rw [hneg, hpos, shifted_laplace_minus F z] at hsplit
    have hplus := shifted_laplace_plus F z
    have hnegPlus :
        -2 * (∫ t in (0 : ℝ)..1,
          (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t)) =
          -(2 * (∫ t in (0 : ℝ)..1,
            (rvachevUp F (2 * t - 1) : ℂ) * Complex.exp (z * t))) := by
      ring
    rw [hnegPlus, hplus] at hsplit
    rw [← hsplit]
    ring
  rw [hderiv] at hparts
  linear_combination hparts

/-- Proposition 2 in complex form: the generating function satisfies
`complexGeneratingFunction F (2 * z) =
complexExpm1Div z * complexGeneratingFunction F z`.  The factor
`complexExpm1Div` gives the totalized value at `z = 0`. -/
theorem proposition_two_formula (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F (2 * z) =
      complexExpm1Div z * complexGeneratingFunction F z := by
  by_cases hz : z = 0
  · subst z
    simp [complexGeneratingFunction]
  rw [complexGeneratingFunction_eq_exp_mul_laplace F hF (2 * z),
    complexGeneratingFunction_eq_exp_mul_laplace F hF z,
    complexExpm1Div_of_ne hz]
  have htwo : 2 * z / 2 = z := by ring
  rw [htwo]
  have hscale := rvachevLaplace_scaling F hF z
  have hexp : Complex.exp z *
      (Complex.exp (z / 2) - Complex.exp (-z / 2)) =
      (Complex.exp z - 1) * Complex.exp (z / 2) := by
    rw [mul_sub, sub_mul, one_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hz).2
  calc
    Complex.exp z * rvachevLaplace F z * z =
        Complex.exp z * (z * rvachevLaplace F z) := by ring
    _ = Complex.exp z *
        ((Complex.exp (z / 2) - Complex.exp (-z / 2)) *
          rvachevLaplace F (z / 2)) := by rw [hscale]
    _ = (Complex.exp z - 1) *
        (Complex.exp (z / 2) * rvachevLaplace F (z / 2)) := by
      calc
        Complex.exp z *
            ((Complex.exp (z / 2) - Complex.exp (-z / 2)) *
              rvachevLaplace F (z / 2)) =
            (Complex.exp z *
              (Complex.exp (z / 2) - Complex.exp (-z / 2))) *
                rvachevLaplace F (z / 2) := by ring
        _ = _ := by rw [hexp]; ring

/-- The real-axis restriction of the complex dilation identity. -/
theorem proposition_two_real_formula
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    generatingFunction F (2 * x) =
      expm1Div x * generatingFunction F x := by
  have h := proposition_two_formula F hF (x : ℂ)
  have htwo : 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [htwo, complexGeneratingFunction_ofReal F (2 * x),
    complexExpm1Div_ofReal x, complexGeneratingFunction_ofReal F x] at h
  exact_mod_cast h

private lemma complexExp_integral_hasSum
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    HasSum
      (fun n : ℕ => ∫ t in (0 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          ((z * (t : ℂ)) ^ n / (n.factorial : ℂ)))
      (∫ t in (0 : ℝ)..1,
        (rvachevUp F t : ℂ) * Complex.exp (z * t)) := by
  let term : ℕ → ℝ → ℂ := fun n t =>
    (rvachevUp F t : ℂ) *
      ((z * (t : ℂ)) ^ n / (n.factorial : ℂ))
  let bound : ℕ → ℝ → ℝ := fun n _ =>
    ‖z ^ n / (n.factorial : ℂ)‖
  apply intervalIntegral.hasSum_integral_of_dominated_convergence bound
  · intro n
    exact ((Complex.continuous_ofReal.comp (rvachev_contDiff F hF).continuous).mul
      (((continuous_const.mul Complex.continuous_ofReal).pow n).div_const _)).aestronglyMeasurable
  · intro n
    filter_upwards with t
    intro ht
    have ht0 : 0 ≤ t := by simpa using ht.1.le
    have ht1 : t ≤ 1 := by simpa using ht.2
    have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact ht1
    have ht_pow : ‖((t : ℂ) ^ n)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) ht_norm
    have hinner :
        ‖(z * (t : ℂ)) ^ n / (n.factorial : ℂ)‖ ≤
          ‖z ^ n / (n.factorial : ℂ)‖ := by
      rw [show (z * (t : ℂ)) ^ n / (n.factorial : ℂ) =
          (z ^ n / (n.factorial : ℂ)) * (t : ℂ) ^ n by
        rw [mul_pow]
        ring]
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) ht_pow
    dsimp [term, bound]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (norm_coe_rvachevUp_le_one F t)).trans hinner
  · filter_upwards with t
    intro _ht
    exact NormedSpace.norm_expSeries_div_summable z
  · have hconst : IntervalIntegrable
        (fun _ : ℝ => ∑' n : ℕ, ‖z ^ n / (n.factorial : ℂ)‖)
        volume 0 1 := intervalIntegrable_const
    simpa only [bound] using hconst
  · filter_upwards with t
    intro _ht
    simpa [term, Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (z * (t : ℂ))).mul_left
        (rvachevUp F t : ℂ)

private lemma halfMoment_succ_seriesTerm_eq_integral
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) (n : ℕ) :
    (halfMoment (n + 1) : ℂ) / ((n + 1).factorial : ℂ) * z ^ (n + 1) =
      z * ∫ t in (0 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          ((z * (t : ℂ)) ^ n / (n.factorial : ℂ)) := by
  have hm := halfMoment_eq_integral_formula_all F hF (n + 1)
  rw [halfMomentIntegral_succ] at hm
  have hmc : (halfMoment (n + 1) : ℂ) =
      (n + 1 : ℂ) *
        (∫ t in (0 : ℝ)..1, t ^ n * rvachevUp F t : ℝ) := by
    exact_mod_cast hm
  have hint :
      (∫ t in (0 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          ((z * (t : ℂ)) ^ n / (n.factorial : ℂ))) =
      (z ^ n / (n.factorial : ℂ)) *
        (∫ t in (0 : ℝ)..1, (t ^ n * rvachevUp F t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    push_cast
    rw [mul_pow]
    ring
  have hcast :
      (∫ t in (0 : ℝ)..1, (t ^ n * rvachevUp F t : ℂ)) =
        ((∫ t in (0 : ℝ)..1, t ^ n * rvachevUp F t : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using
      (intervalIntegral.integral_ofReal
        (f := fun t : ℝ => t ^ n * rvachevUp F t) (a := 0) (b := 1))
  rw [hmc, hint, hcast, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- Equation (17): the half moments are the Taylor coefficients of the
complex generating function. -/
theorem complexGeneratingFunction_eq_series_formula
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z = halfMomentGeneratingSeries z := by
  let coeff : ℕ → ℂ := fun n =>
    (halfMoment n : ℂ) / (n.factorial : ℂ) * z ^ n
  have htail : HasSum (fun n : ℕ => coeff (n + 1))
      (z * ∫ t in (0 : ℝ)..1,
        (rvachevUp F t : ℂ) * Complex.exp (z * t)) := by
    apply (complexExp_integral_hasSum F hF z).mul_left z |>.congr_fun
    intro n
    exact halfMoment_succ_seriesTerm_eq_integral F hF z n
  have hfull : HasSum coeff (complexGeneratingFunction F z) := by
    simpa [coeff, complexGeneratingFunction, halfMoment_zero] using htail.zero_add
  rw [halfMomentGeneratingSeries]
  exact hfull.tsum_eq.symm

private lemma integral_rvachev_mul_eq_interval
    (F : BoundedFabius) (hF : IsFabius F) (g : ℝ → ℂ) :
    (∫ x : ℝ, (rvachevUp F x : ℂ) * g x) =
      ∫ x in (-1 : ℝ)..1, (rvachevUp F x : ℂ) * g x := by
  apply integral_eq_interval_of_support_subset_rvachevUp F hF
  intro x hx
  change rvachevUp F x ≠ 0
  intro hzero
  exact hx (by simp [hzero])

private lemma rvachevFourier_expansion_hasSum
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    HasSum
      (fun m : ℕ => ∫ t in (-1 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          (((-2 * Real.pi * Complex.I * z) * (t : ℂ)) ^ m /
            (m.factorial : ℂ)))
      (∫ t in (-1 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          Complex.exp ((-2 * Real.pi * Complex.I * z) * t)) := by
  let c : ℂ := -2 * Real.pi * Complex.I * z
  let term : ℕ → ℝ → ℂ := fun m t =>
    (rvachevUp F t : ℂ) * ((c * (t : ℂ)) ^ m / (m.factorial : ℂ))
  let bound : ℕ → ℝ → ℝ := fun m _ => ‖c ^ m / (m.factorial : ℂ)‖
  apply intervalIntegral.hasSum_integral_of_dominated_convergence bound
  · intro m
    exact ((Complex.continuous_ofReal.comp (rvachev_contDiff F hF).continuous).mul
      (((continuous_const.mul Complex.continuous_ofReal).pow m).div_const _)).aestronglyMeasurable
  · intro m
    filter_upwards with t
    intro ht
    have htLower : -1 ≤ t := by simpa using ht.1.le
    have htUpper : t ≤ 1 := by simpa using ht.2
    have htNorm : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith, htUpper⟩
    have htPow : ‖((t : ℂ) ^ m)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) htNorm
    have hinner :
        ‖(c * (t : ℂ)) ^ m / (m.factorial : ℂ)‖ ≤
          ‖c ^ m / (m.factorial : ℂ)‖ := by
      rw [show (c * (t : ℂ)) ^ m / (m.factorial : ℂ) =
          (c ^ m / (m.factorial : ℂ)) * (t : ℂ) ^ m by
        rw [mul_pow]
        ring]
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) htPow
    dsimp [term, bound]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (norm_coe_rvachevUp_le_one F t)).trans hinner
  · filter_upwards with t
    intro _ht
    exact NormedSpace.norm_expSeries_div_summable c
  · have hconst : IntervalIntegrable
        (fun _ : ℝ => ∑' m : ℕ, ‖c ^ m / (m.factorial : ℂ)‖)
        volume (-1) 1 := intervalIntegrable_const
    simpa only [bound] using hconst
  · filter_upwards with t
    intro _ht
    simpa [term, c, Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (c * (t : ℂ))).mul_left
        (rvachevUp F t : ℂ)

private lemma fourierSeriesTerm_integral_factor
    (F : BoundedFabius) (z : ℂ) (m : ℕ) :
    (∫ t in (-1 : ℝ)..1,
      (rvachevUp F t : ℂ) *
        (((-2 * Real.pi * Complex.I * z) * (t : ℂ)) ^ m /
          (m.factorial : ℂ))) =
      ((-2 * Real.pi * Complex.I * z) ^ m / (m.factorial : ℂ)) *
        ((∫ t in (-1 : ℝ)..1, t ^ m * rvachevUp F t : ℝ) : ℂ) := by
  have hcast :
      (∫ t in (-1 : ℝ)..1, (t ^ m * rvachevUp F t : ℂ)) =
        ((∫ t in (-1 : ℝ)..1, t ^ m * rvachevUp F t : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using
      (intervalIntegral.integral_ofReal
        (f := fun t : ℝ => t ^ m * rvachevUp F t) (a := -1) (b := 1))
  rw [← hcast, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  push_cast
  rw [mul_pow]
  ring

private lemma neg_two_pi_I_pow_even (z : ℂ) (n : ℕ) :
    (-2 * Real.pi * Complex.I * z) ^ (2 * n) =
      (-1 : ℂ) ^ n * (2 * Real.pi * z) ^ (2 * n) := by
  rw [show (-2 * Real.pi * Complex.I * z : ℂ) =
      (-Complex.I) * (2 * Real.pi * z) by ring]
  rw [mul_pow]
  congr 1
  rw [pow_mul]
  congr 1
  rw [pow_two, neg_mul_neg, Complex.I_mul_I]

private lemma fourierSeriesTerm_odd_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) (n : ℕ) :
    (∫ t in (-1 : ℝ)..1,
      (rvachevUp F t : ℂ) *
        (((-2 * Real.pi * Complex.I * z) * (t : ℂ)) ^ (2 * n + 1) /
          ((2 * n + 1).factorial : ℂ))) = 0 := by
  rw [fourierSeriesTerm_integral_factor F z (2 * n + 1)]
  rw [intervalIntegral_odd_pow_mul_rvachev_eq_zero F hF n]
  simp

private lemma fourierSeriesTerm_even_eq_moment
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) (n : ℕ) :
    (∫ t in (-1 : ℝ)..1,
      (rvachevUp F t : ℂ) *
        (((-2 * Real.pi * Complex.I * z) * (t : ℂ)) ^ (2 * n) /
          ((2 * n).factorial : ℂ))) =
      (-1 : ℂ) ^ n * (moment n : ℂ) /
        ((2 * n).factorial : ℂ) * (2 * Real.pi * z) ^ (2 * n) := by
  rw [fourierSeriesTerm_integral_factor F z (2 * n)]
  have hm : (moment n : ℝ) =
      ∫ t : ℝ, t ^ (2 * n) * rvachevUp F t := by
    simpa [momentIntegral] using moment_eq_integral_formula F hF n
  have hloc := integral_pow_mul_rvachev_eq_interval F hF (2 * n)
  have hmoment : (∫ t in (-1 : ℝ)..1,
      t ^ (2 * n) * rvachevUp F t) = (moment n : ℝ) :=
    (hm.trans hloc).symm
  rw [hmoment, neg_two_pi_I_pow_even]
  push_cast
  ring

/-- A convergent series whose odd terms vanish has the same sum along its
even subsequence. -/
theorem hasSum_even_of_odd_eq_zero
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℕ → E} {a : E}
    (h : HasSum f a) (hodd : ∀ n, f (2 * n + 1) = 0) :
    HasSum (fun n ↦ f (2 * n)) a := by
  change HasSum (f ∘ (fun n : ℕ ↦ 2 * n)) a
  rw [(mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · exact h
  · intro m hm
    rw [range_two_mul, Set.mem_setOf_eq, Nat.not_even_iff_odd] at hm
    obtain ⟨n, rfl⟩ := hm
    exact hodd n

/-- The Fourier transform of Rvachev's function is its even-moment series. -/
theorem rvachevFourier_eq_momentSeries
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevFourier F z = rvachevMomentSeries z := by
  let term : ℕ → ℂ := fun m =>
    ∫ t in (-1 : ℝ)..1,
      (rvachevUp F t : ℂ) *
        (((-2 * Real.pi * Complex.I * z) * (t : ℂ)) ^ m /
          (m.factorial : ℂ))
  have hall : HasSum term
      (∫ t in (-1 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          Complex.exp ((-2 * Real.pi * Complex.I * z) * t)) := by
    exact rvachevFourier_expansion_hasSum F hF z
  have heven : HasSum (fun n : ℕ => term (2 * n))
      (∫ t in (-1 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          Complex.exp ((-2 * Real.pi * Complex.I * z) * t)) :=
    hasSum_even_of_odd_eq_zero hall fun n =>
      fourierSeriesTerm_odd_eq_zero F hF z n
  have hmoments : HasSum
      (fun n : ℕ => (-1 : ℂ) ^ n * (moment n : ℂ) /
        ((2 * n).factorial : ℂ) * (2 * Real.pi * z) ^ (2 * n))
      (∫ t in (-1 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          Complex.exp ((-2 * Real.pi * Complex.I * z) * t)) := by
    apply heven.congr_fun
    intro n
    exact (fourierSeriesTerm_even_eq_moment F hF z n).symm
  have hfourier : rvachevFourier F z =
      ∫ t in (-1 : ℝ)..1,
        (rvachevUp F t : ℂ) *
          Complex.exp ((-2 * Real.pi * Complex.I * z) * t) := by
    rw [rvachevFourier]
    calc
      (∫ t : ℝ, (rvachevUp F t : ℂ) *
          Complex.exp (-2 * Real.pi * Complex.I * t * z)) =
          ∫ t : ℝ, (rvachevUp F t : ℂ) *
            Complex.exp ((-2 * Real.pi * Complex.I * z) * t) := by
        apply integral_congr_ae
        filter_upwards with t
        congr 2
        ring
      _ = ∫ t in (-1 : ℝ)..1,
          (rvachevUp F t : ℂ) *
            Complex.exp ((-2 * Real.pi * Complex.I * z) * t) :=
        integral_rvachev_mul_eq_interval F hF _
  rw [hfourier, rvachevMomentSeries]
  exact hmoments.tsum_eq.symm

end Fabius
