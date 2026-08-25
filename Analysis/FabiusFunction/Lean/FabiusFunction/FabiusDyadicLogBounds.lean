import FabiusFunction.PaperStatements
import FabiusFunction.StepMeasureBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Coarse logarithmic bounds at dyadic arguments

This module proves a rigorous natural-index anchor for the log-squared decay
claimed in equation (11) of the K-fold Thue--Morse draft.  It does not use the
separate asymptotic draft's unsupported periodic ansatz.  Instead, the exact identity

`halfMoment n = n! * 2^(choose n 2) * F(2⁻ⁿ)`

is combined with the elementary integral bounds

`2⁻⁽ⁿ⁺¹⁾ ≤ halfMoment n ≤ 1`.

The resulting explicit estimate is

`|log F(2⁻ⁿ) + (log 2 / 2) n²| ≤ 3 n log (n + 1)`

for every `n ≥ 1`.  As a headline asymptotic corollary, the normalized
logarithm along the dyadic sequence tends to `-(log 2) / 2`.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Set MeasureTheory

namespace Fabius

noncomputable section

private lemma rvachevUp_ge_half_on_zero_half
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    1 / 2 ≤ rvachevUp F t := by
  by_cases ht0 : t = 0
  · subst t
    rw [rvachevUp, if_pos le_rfl]
    simp only [zero_add]
    rw [hF.one_of_one_le 1 le_rfl]
    norm_num
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [rvachevUp, if_neg (not_le.mpr htpos)]
    have hmono := fabius_monotone F hF
      (show (1 / 2 : ℝ) ≤ 1 - t by linarith [ht.2])
    rwa [fabius_half F hF] at hmono

/-- The half moments are at most one. -/
theorem halfMoment_real_le_one (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    (halfMoment n : ℝ) ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 m] at hn ⊢
  rw [halfMoment_eq_integral_formula_all F hF (m + 1)]
  change ((m + 1 : ℕ) : ℝ) *
      (∫ t in (0 : ℝ)..1, t ^ m * rvachevUp F t) ≤ 1
  have hmono :
      (∫ t in (0 : ℝ)..1, t ^ m * rvachevUp F t) ≤
        ∫ t in (0 : ℝ)..1, t ^ m := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((pow_mul_rvachev_continuous F hF m).intervalIntegrable 0 1)
      ((continuous_id.pow m).intervalIntegrable 0 1)
    intro t ht
    change t ^ m * rvachevUp F t ≤ t ^ m
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (rvachevUp_le_one F t) (pow_nonneg ht.1 m)
  have hpow : (∫ t in (0 : ℝ)..1, t ^ m) = 1 / ((m + 1 : ℕ) : ℝ) := by
    rw [integral_pow]
    norm_num
  calc
    ((m + 1 : ℕ) : ℝ) *
        (∫ t in (0 : ℝ)..1, t ^ m * rvachevUp F t) ≤
        ((m + 1 : ℕ) : ℝ) * (∫ t in (0 : ℝ)..1, t ^ m) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 1 := by rw [hpow]; field_simp

/-- A crude but explicit lower bound on the half moments. -/
theorem halfMoment_real_lower (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (halfMoment n : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 m] at hn ⊢
  rw [halfMoment_eq_integral_formula_all F hF (m + 1)]
  change ((2 : ℝ) ^ (m + 1 + 1))⁻¹ ≤
    ((m + 1 : ℕ) : ℝ) *
      (∫ t in (0 : ℝ)..1, t ^ m * rvachevUp F t)
  have hcont := pow_mul_rvachev_continuous F hF m
  have hsmall :
      (∫ t in (0 : ℝ)..(1 / 2), (1 / 2 : ℝ) * t ^ m) ≤
        ∫ t in (0 : ℝ)..(1 / 2), t ^ m * rvachevUp F t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 (1 / 2))
      (hcont.intervalIntegrable 0 (1 / 2))
    intro t ht
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right (rvachevUp_ge_half_on_zero_half F hF ht)
        (pow_nonneg ht.1 m)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        (fun t : ℝ => t ^ m * rvachevUp F t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (pow_nonneg (le_of_lt ht.1) m) (rvachevUp_nonneg F t)
  have hlarge :
      (∫ t in (0 : ℝ)..(1 / 2), t ^ m * rvachevUp F t) ≤
        ∫ t in (0 : ℝ)..1, t ^ m * rvachevUp F t :=
    intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
      hnonneg (hcont.intervalIntegrable 0 1)
  calc
    ((2 : ℝ) ^ (m + 1 + 1))⁻¹ =
        ((m + 1 : ℕ) : ℝ) *
          (∫ t in (0 : ℝ)..(1 / 2), (1 / 2 : ℝ) * t ^ m) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num [div_pow]
      field_simp
      ring
    _ ≤ ((m + 1 : ℕ) : ℝ) *
        (∫ t in (0 : ℝ)..(1 / 2), t ^ m * rvachevUp F t) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ ≤ ((m + 1 : ℕ) : ℝ) *
        (∫ t in (0 : ℝ)..1, t ^ m * rvachevUp F t) :=
      mul_le_mul_of_nonneg_left hlarge (by positivity)

/-- The logarithm of a positive half moment is nonpositive. -/
theorem log_halfMoment_le_zero (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    Real.log (halfMoment n : ℝ) ≤ 0 := by
  exact Real.log_nonpos (by exact_mod_cast (halfMoment_pos n).le)
    (halfMoment_real_le_one F hF n hn)

/-- The crude lower half-moment bound in logarithmic form. -/
theorem neg_succ_mul_log_two_le_log_halfMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    -((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (halfMoment n : ℝ) := by
  calc
    -((n + 1 : ℕ) : ℝ) * Real.log 2 =
        Real.log (((2 : ℝ) ^ (n + 1))⁻¹) := by
      rw [Real.log_inv, Real.log_pow]
      ring
    _ ≤ Real.log (halfMoment n : ℝ) :=
      Real.log_le_log (by positivity) (halfMoment_real_lower F hF n hn)

/-- Exact logarithmic decomposition of the dyadic Fabius value. -/
theorem log_fabius_inverse_two_pow_eq
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) =
      Real.log (halfMoment n : ℝ) - Real.log (n.factorial : ℝ) -
        (n.choose 2 : ℝ) * Real.log 2 := by
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ n.choose 2 ≠ 0 := by positivity
  have hf : fabiusReal F (((2 : ℝ) ^ n)⁻¹) ≠ 0 :=
    ne_of_gt (fabius_pos_of_pos F hF (by positivity))
  have hlog := congrArg Real.log (halfMoment_eq_fabius_formula F hF n)
  rw [Real.log_mul (mul_ne_zero hfac hpow) hf,
    Real.log_mul hfac hpow, Real.log_pow] at hlog
  linarith

/-- The centered logarithmic error along the dyadic sequence `x = 2⁻ⁿ`. -/
noncomputable def dyadicLogError (F : BoundedFabius) (n : ℕ) : ℝ :=
  Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) +
    Real.log 2 / 2 * (n : ℝ) ^ 2

/-- After centering by the quadratic term, only the half moment, the factorial,
and a linear correction remain. -/
theorem dyadicLogError_eq
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    dyadicLogError F n =
      Real.log (halfMoment n : ℝ) - Real.log (n.factorial : ℝ) +
        (n : ℝ) / 2 * Real.log 2 := by
  rw [dyadicLogError, log_fabius_inverse_two_pow_eq F hF n,
    Nat.cast_choose_two ℝ]
  ring

private lemma log_factorial_nonneg (n : ℕ) :
    0 ≤ Real.log (n.factorial : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast Nat.factorial_pos n

private lemma log_factorial_le_self_mul_log (n : ℕ) (_hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) hfac
  simpa [Real.log_pow] using hlog

/-- Explicit two-sided version of the coarse log-squared estimate at dyadic
arguments.  The constant `3` is deliberately elementary rather than sharp. -/
theorem dyadicLogError_bounds
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    -3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ≤ dyadicLogError F n ∧
      dyadicLogError F n ≤ 3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hn1one : (1 : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hlogn1_nonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg hn1one
  have hlogn_le : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log hnpos (by exact_mod_cast (Nat.le_succ n))
  have hlogtwo_le : Real.log 2 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n + 1 by omega))
  have hnlog_le :
      (n : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlogn_le hnpos.le
  have hcoeff : (n : ℝ) / 2 + 1 ≤ 2 * (n : ℝ) := by linarith
  have hcoeff_logtwo :
      ((n : ℝ) / 2 + 1) * Real.log 2 ≤
        2 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) := by
    calc
      ((n : ℝ) / 2 + 1) * Real.log 2 ≤
          ((n : ℝ) / 2 + 1) * Real.log ((n + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogtwo_le (by linarith)
      _ ≤ 2 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff hlogn1_nonneg
  have hhalf_logtwo :
      (n : ℝ) / 2 * Real.log 2 ≤
        3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlogtwo_le
      (show 0 ≤ (n : ℝ) / 2 by positivity)
    nlinarith
  rw [dyadicLogError_eq F hF n]
  constructor
  · have hd := neg_succ_mul_log_two_le_log_halfMoment F hF n hn
    have hfac := log_factorial_le_self_mul_log n hn
    push_cast at hd
    nlinarith
  · have hd := log_halfMoment_le_zero F hF n hn
    have hfac := log_factorial_nonneg n
    linarith

/-- Coarse log-squared asymptotics along dyadic integer arguments. -/
theorem abs_dyadicLogError_le
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    |Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) +
        Real.log 2 / 2 * (n : ℝ) ^ 2| ≤
      3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) := by
  rw [← dyadicLogError]
  rw [abs_le]
  have h := dyadicLogError_bounds F hF n hn
  constructor
  · nlinarith [h.1]
  · exact h.2

/-- The centered dyadic logarithmic error is negligible after division by
`n²`. -/
theorem normalized_dyadicLogError_tendsto_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    Filter.Tendsto (fun n : ℕ => dyadicLogError F n / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  have harg :
      Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hlogdiv :
      Filter.Tendsto
        (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp harg
  have hmajorant :
      Filter.Tendsto
        (fun n : ℕ => 6 *
          (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using hlogdiv.const_mul 6
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun n : ℕ => 6 *
      (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
    (Filter.Eventually.of_forall fun n => norm_nonneg _)
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn1pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hlognonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
    have habs := abs_dyadicLogError_le F hF n hn
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hnpos]
    calc
      |dyadicLogError F n| / (n : ℝ) ^ 2 ≤
          (3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) / (n : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right habs (sq_nonneg (n : ℝ))
      _ = 3 * Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
        field_simp
      _ ≤ 6 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
        rw [show 6 * (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
          6 * Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) by ring]
        rw [div_le_div_iff₀ hnpos hn1pos]
        push_cast
        have hprod :
            0 ≤ ((n : ℝ) - 1) * Real.log ((n + 1 : ℕ) : ℝ) :=
          mul_nonneg (sub_nonneg.mpr hnone) hlognonneg
        push_cast at hprod
        nlinarith
  · exact hmajorant

/-- The normalized logarithm along `x = 2⁻ⁿ` has the expected quadratic
leading coefficient. -/
theorem normalized_log_fabius_inverse_two_pow_tendsto
    (F : BoundedFabius) (hF : IsFabius F) :
    Filter.Tendsto
      (fun n : ℕ =>
        Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) / (n : ℝ) ^ 2)
      Filter.atTop (nhds (-(Real.log 2) / 2)) := by
  have h := (normalized_dyadicLogError_tendsto_zero F hF).sub_const
    (Real.log 2 / 2)
  have h' :
      Filter.Tendsto
        (fun n : ℕ => dyadicLogError F n / (n : ℝ) ^ 2 - Real.log 2 / 2)
        Filter.atTop (nhds (-(Real.log 2) / 2)) := by
    convert h using 1
    ring_nf
  apply h'.congr'
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold dyadicLogError
  field_simp
  ring

end

end Fabius
