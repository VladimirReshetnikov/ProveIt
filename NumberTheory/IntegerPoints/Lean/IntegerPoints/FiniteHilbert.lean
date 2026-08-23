import IntegerPoints.KuzminLandau
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A finite Hilbert inequality

This module develops the sharp finite Hilbert inequality needed by
Graham–Kolesnik's Appendix A mean-square estimate.  Its proof uses the
sawtooth weight `1/2 - x` on `[0,1]` and finite Fourier orthogonality.
-/

open Real Finset MeasureTheory intervalIntegral

namespace LeanProofs.IntegerPoints

namespace FiniteHilbert

/-- Orthogonality of the integer Fourier characters on `[0,1]`. -/
theorem integral_e_int_mul (k : ℤ) :
    (∫ x in (0 : ℝ)..1, e ((k : ℝ) * x)) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [e]
  · rw [if_neg hk]
    set c : ℂ := (((2 * π * (k : ℝ) : ℝ) : ℂ) * Complex.I) with hc
    have hreal : (2 * π * (k : ℝ) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr hk)
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (by exact_mod_cast hreal) Complex.I_ne_zero
    have hefun : (fun x : ℝ => e ((k : ℝ) * x)) =
        fun x : ℝ => Complex.exp (c * x) := by
      funext x
      rw [e, hc]
      push_cast
      congr 1
      ring
    rw [hefun, integral_exp_mul_complex hc0]
    have he1 : Complex.exp (c * (1 : ℝ)) = 1 := by
      calc
        Complex.exp (c * (1 : ℝ)) = e (k : ℝ) := by
          rw [e, hc]
          push_cast
          congr 1
          ring
        _ = 1 := KL.e_int k
    rw [he1]
    simp

/-- The nonzero Fourier coefficients of the centered sawtooth on `[0,1]`.

The sign convention here matches `e x = exp (2 π i x)`: for `k ≠ 0` the
coefficient is `i / (2 π k)`. -/
theorem integral_sawtooth_mul_e_int (k : ℤ) :
    (∫ x in (0 : ℝ)..1,
        (((1 / 2 - x : ℝ) : ℂ) * e ((k : ℝ) * x))) =
      if k = 0 then 0 else Complex.I / (2 * π * (k : ℝ)) := by
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl]
    simp only [Int.cast_zero, zero_mul]
    rw [show e 0 = 1 by simp [e]]
    simp only [mul_one]
    rw [intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id]
    rw [intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    norm_num
  · rw [if_neg hk]
    set c : ℂ := (((2 * π * (k : ℝ) : ℝ) : ℂ) * Complex.I) with hc
    have hreal : (2 * π * (k : ℝ) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr hk)
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (by exact_mod_cast hreal) Complex.I_ne_zero
    have hefun : (fun x : ℝ => e ((k : ℝ) * x)) =
        fun x : ℝ => Complex.exp (c * x) := by
      funext x
      rw [e, hc]
      push_cast
      congr 1
      ring
    have hepoint (x : ℝ) : e ((k : ℝ) * x) = Complex.exp (c * x) :=
      congrFun hefun x
    simp_rw [hepoint]
    let F : ℝ → ℂ := fun x =>
      Complex.exp (c * x) *
        ((((1 / 2 - x : ℝ) : ℂ) / c) + 1 / c ^ 2)
    have hF : ∀ x : ℝ,
        HasDerivAt F
          (((1 / 2 - x : ℝ) : ℂ) * Complex.exp (c * x)) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa only [mul_one] using!
          ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
      have hexp : HasDerivAt (fun y : ℝ => Complex.exp (c * y))
          (Complex.exp (c * x) * c) x :=
        (Complex.hasDerivAt_exp _).comp x hlin
      have hsawReal : HasDerivAt (fun y : ℝ => 1 / 2 - y) (-1) x :=
        (hasDerivAt_id x).const_sub (1 / 2 : ℝ)
      have hsaw : HasDerivAt (fun y : ℝ => ((1 / 2 - y : ℝ) : ℂ)) (-1) x :=
        by
          convert hsawReal.ofReal_comp using 1
          norm_num
      have hinner : HasDerivAt
          (fun y : ℝ => (((1 / 2 - y : ℝ) : ℂ) / c) + 1 / c ^ 2)
          ((-1 : ℂ) / c + 0) x :=
        (hsaw.div_const c).add (hasDerivAt_const x (1 / c ^ 2))
      have hprod := hexp.mul hinner
      convert hprod using 1
      all_goals try rfl
      field_simp [hc0]
      ring
    have hint : IntervalIntegrable
        (fun x : ℝ => (((1 / 2 - x : ℝ) : ℂ) * Complex.exp (c * x)))
        volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint]
    have he0 : Complex.exp (c * (0 : ℝ)) = 1 := by simp
    have he1 : Complex.exp (c * (1 : ℝ)) = 1 := by
      calc
        Complex.exp (c * (1 : ℝ)) = e (k : ℝ) := by
          rw [e, hc]
          push_cast
          congr 1
          ring
        _ = 1 := KL.e_int k
    change Complex.exp (c * (1 : ℝ)) *
          ((((1 / 2 - (1 : ℝ) : ℝ) : ℂ) / c) + 1 / c ^ 2) -
        Complex.exp (c * (0 : ℝ)) *
          ((((1 / 2 - (0 : ℝ) : ℝ) : ℂ) / c) + 1 / c ^ 2) = _
    rw [he0, he1]
    rw [hc]
    push_cast
    field_simp [hreal, Complex.I_ne_zero]
    rw [show Complex.I ^ 3 = -Complex.I by
      rw [pow_succ, Complex.I_sq]
      ring]
    ring

/-- A finite trigonometric polynomial with the repository's `e(x)` convention. -/
noncomputable def fourierPoly (S : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, a n * e ((n : ℝ) * x)

/-- A finite trigonometric polynomial is continuous. -/
theorem continuous_fourierPoly (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (fourierPoly S a) := by
  unfold fourierPoly
  refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
  unfold e
  fun_prop

/-- Expand the squared modulus of a finite trigonometric polynomial into its
double Fourier sum.  Integer differences avoid truncated natural subtraction. -/
theorem fourierPoly_mul_conj (S : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x) =
      ∑ m ∈ S, ∑ n ∈ S,
        a m * starRingEnd ℂ (a n) *
          e (((m : ℤ) - (n : ℤ) : ℤ) * x) := by
  unfold fourierPoly
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, ← KL.e_neg]
  calc
    (a m * e ((m : ℝ) * x)) *
        (starRingEnd ℂ (a n) * e (-((n : ℝ) * x))) =
      a m * starRingEnd ℂ (a n) *
        (e ((m : ℝ) * x) * e (-((n : ℝ) * x))) := by ring
    _ = a m * starRingEnd ℂ (a n) *
        e (((m : ℤ) - (n : ℤ) : ℤ) * x) := by
      rw [← KL.e_add]
      congr 2
      push_cast
      ring

/-- Complex-valued finite Parseval identity for `fourierPoly`. -/
theorem integral_fourierPoly_mul_conj (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1,
        fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x)) =
      ∑ n ∈ S, a n * starRingEnd ℂ (a n) := by
  simp_rw [fourierPoly_mul_conj]
  have hterm (m n : ℕ) : IntervalIntegrable
      (fun x : ℝ =>
        a m * starRingEnd ℂ (a n) *
          e (((m : ℤ) - (n : ℤ) : ℤ) * x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold e
    fun_prop
  have hinner (m : ℕ) : IntervalIntegrable
      (fun x : ℝ => ∑ n ∈ S,
        a m * starRingEnd ℂ (a n) *
          e (((m : ℤ) - (n : ℤ) : ℤ) * x)) volume 0 1 := by
    rw [show (fun x : ℝ => ∑ n ∈ S,
        a m * starRingEnd ℂ (a n) *
          e (((m : ℤ) - (n : ℤ) : ℤ) * x)) =
      ∑ n ∈ S, (fun x : ℝ =>
        a m * starRingEnd ℂ (a n) *
          e (((m : ℤ) - (n : ℤ) : ℤ) * x)) by
        funext x
        simp]
    exact IntervalIntegrable.sum S (fun n _ => hterm m n)
  rw [intervalIntegral.integral_finsetSum
    (f := fun m x => ∑ n ∈ S,
      a m * starRingEnd ℂ (a n) *
        e (((m : ℤ) - (n : ℤ) : ℤ) * x))
    (fun m _ => hinner m)]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_finsetSum
    (f := fun n x => a m * starRingEnd ℂ (a n) *
      e (((m : ℤ) - (n : ℤ) : ℤ) * x))
    (fun n _ => hterm m n)]
  rw [Finset.sum_eq_single_of_mem m hm]
  · rw [intervalIntegral.integral_const_mul, integral_e_int_mul]
    simp
  · intro n hn hnm
    rw [intervalIntegral.integral_const_mul, integral_e_int_mul]
    have hk : (m : ℤ) - (n : ℤ) ≠ 0 := by omega
    rw [if_neg hk, mul_zero]

/-- Finite Parseval identity on `[0,1]`. -/
theorem finite_parseval (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖fourierPoly S a x‖ ^ 2) =
      ∑ n ∈ S, ‖a n‖ ^ 2 := by
  refine Complex.ofReal_injective ?_
  calc
    (((∫ x in (0 : ℝ)..1, ‖fourierPoly S a x‖ ^ 2) : ℝ) : ℂ) =
        ∫ x in (0 : ℝ)..1, ((‖fourierPoly S a x‖ ^ 2 : ℝ) : ℂ) :=
      (intervalIntegral.integral_ofReal).symm
    _ = ∫ x in (0 : ℝ)..1,
        fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change ((‖fourierPoly S a x‖ ^ 2 : ℝ) : ℂ) =
        fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x)
      push_cast
      exact (Complex.mul_conj' (fourierPoly S a x)).symm
    _ = ∑ n ∈ S, a n * starRingEnd ℂ (a n) :=
      integral_fourierPoly_mul_conj S a
    _ = (((∑ n ∈ S, ‖a n‖ ^ 2) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun n _ => Complex.mul_conj' (a n)

/-- The sawtooth coefficient in the natural-index difference form used by the
finite Hilbert kernel.  The reversed denominator is the consequence of the
positive coefficient in `integral_sawtooth_mul_e_int`. -/
theorem integral_sawtooth_nat_sub (m n : ℕ) :
    (∫ x in (0 : ℝ)..1,
        (((1 / 2 - x : ℝ) : ℂ) *
          e (((m : ℝ) - (n : ℝ)) * x))) =
      if m = n then 0 else
        1 / ((2 * π * Complex.I) * ((n : ℂ) - (m : ℂ))) := by
  have hphase (x : ℝ) :
      e (((m : ℝ) - (n : ℝ)) * x) =
        e (((m : ℤ) - (n : ℤ) : ℤ) * x) := by
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  rw [integral_sawtooth_mul_e_int]
  by_cases hmn : m = n
  · subst n
    simp
  · have hk : (m : ℤ) - (n : ℤ) ≠ 0 := by omega
    rw [if_neg hk, if_neg hmn]
    have hdiff : ((n : ℂ) - (m : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast Ne.symm hmn
    have hdiff' : ((m : ℂ) - (n : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast hmn
    have hkreal : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast hk
    have hπ : ((π : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp [hdiff, hdiff', hkreal, hπ, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring

/-- Exact sawtooth representation of the finite Hilbert form. -/
theorem finite_hilbert_identity (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ m ∈ S, ∑ n ∈ S.filter (fun n => n ≠ m),
        a m * starRingEnd ℂ (a n) / ((n : ℂ) - (m : ℂ))) =
      (2 * π * Complex.I) *
        ∫ x in (0 : ℝ)..1,
          (((1 / 2 - x : ℝ) : ℂ) *
            (fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x))) := by
  classical
  let weightedTerm : ℕ → ℕ → ℝ → ℂ := fun m n x =>
    (((1 / 2 - x : ℝ) : ℂ) *
      (a m * starRingEnd ℂ (a n) *
        e (((m : ℤ) - (n : ℤ) : ℤ) * x)))
  have hphase (m n : ℕ) (x : ℝ) :
      e (((m : ℤ) - (n : ℤ) : ℤ) * x) =
        e (((m : ℝ) - (n : ℝ)) * x) := by
    congr 1
    push_cast
    ring
  have hcoefficient (m n : ℕ) :
      (∫ x in (0 : ℝ)..1, weightedTerm m n x) =
        a m * starRingEnd ℂ (a n) *
          (if m = n then 0 else
            1 / ((2 * π * Complex.I) * ((n : ℂ) - (m : ℂ)))) := by
    calc
      (∫ x in (0 : ℝ)..1, weightedTerm m n x) =
          ∫ x in (0 : ℝ)..1,
            (a m * starRingEnd ℂ (a n)) *
              (((1 / 2 - x : ℝ) : ℂ) *
                e (((m : ℝ) - (n : ℝ)) * x)) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [weightedTerm]
        rw [hphase]
        ring
      _ = (a m * starRingEnd ℂ (a n)) *
          ∫ x in (0 : ℝ)..1,
            (((1 / 2 - x : ℝ) : ℂ) *
              e (((m : ℝ) - (n : ℝ)) * x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_sawtooth_nat_sub]
  have hterm (m n : ℕ) : IntervalIntegrable (weightedTerm m n) volume 0 1 := by
    apply Continuous.intervalIntegrable
    simp only [weightedTerm]
    unfold e
    fun_prop
  have hinner (m : ℕ) : IntervalIntegrable
      (fun x : ℝ => ∑ n ∈ S, weightedTerm m n x) volume 0 1 := by
    rw [show (fun x : ℝ => ∑ n ∈ S, weightedTerm m n x) =
      ∑ n ∈ S, weightedTerm m n by
        funext x
        simp]
    exact IntervalIntegrable.sum S (fun n _ => hterm m n)
  have hexpand (x : ℝ) :
      (((1 / 2 - x : ℝ) : ℂ) *
          (fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x))) =
        ∑ m ∈ S, ∑ n ∈ S, weightedTerm m n x := by
    rw [fourierPoly_mul_conj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
  have hintegral :
      (∫ x in (0 : ℝ)..1,
          (((1 / 2 - x : ℝ) : ℂ) *
            (fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x)))) =
        ∑ m ∈ S, ∑ n ∈ S,
          a m * starRingEnd ℂ (a n) *
            (if m = n then 0 else
              1 / ((2 * π * Complex.I) * ((n : ℂ) - (m : ℂ)))) := by
    calc
      (∫ x in (0 : ℝ)..1,
          (((1 / 2 - x : ℝ) : ℂ) *
            (fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x)))) =
          ∫ x in (0 : ℝ)..1,
            ∑ m ∈ S, ∑ n ∈ S, weightedTerm m n x := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hexpand x
      _ = ∑ m ∈ S, ∫ x in (0 : ℝ)..1,
          ∑ n ∈ S, weightedTerm m n x := by
        rw [intervalIntegral.integral_finsetSum
          (f := fun m x => ∑ n ∈ S, weightedTerm m n x)
          (fun m _ => hinner m)]
      _ = ∑ m ∈ S, ∑ n ∈ S,
          ∫ x in (0 : ℝ)..1, weightedTerm m n x := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [intervalIntegral.integral_finsetSum
          (f := fun n x => weightedTerm m n x)
          (fun n _ => hterm m n)]
      _ = _ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        exact Finset.sum_congr rfl fun n _ => hcoefficient m n
  rw [hintegral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hmn : m = n
  · subst n
    simp
  · rw [if_pos (Ne.symm hmn), if_neg hmn]
    have hdiff : ((n : ℂ) - (m : ℂ)) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast Ne.symm hmn
    have hπ : ((π : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    field_simp [hdiff, hπ, Complex.I_ne_zero]

/-- The sharp finite Hilbert inequality for integer indices. -/
theorem finite_hilbert (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ m ∈ S, ∑ n ∈ S.filter (fun n => n ≠ m),
        a m * starRingEnd ℂ (a n) / ((n : ℂ) - (m : ℂ))‖ ≤
      π * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let P : ℝ → ℂ := fourierPoly S a
  have hPcont : Continuous P := by
    exact continuous_fourierPoly S a
  have hweighted : Continuous (fun x : ℝ =>
      (((1 / 2 - x : ℝ) : ℂ) *
        (P x * starRingEnd ℂ (P x)))) := by
    fun_prop
  have hmajorant : Continuous (fun x : ℝ =>
      (1 / 2 : ℝ) * ‖P x‖ ^ 2) :=
    continuous_const.mul (hPcont.norm.pow 2)
  have hintegral :
      ‖∫ x in (0 : ℝ)..1,
          (((1 / 2 - x : ℝ) : ℂ) *
            (P x * starRingEnd ℂ (P x)))‖ ≤
        (1 / 2 : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
    calc
      ‖∫ x in (0 : ℝ)..1,
          (((1 / 2 - x : ℝ) : ℂ) *
            (P x * starRingEnd ℂ (P x)))‖ ≤
          ∫ x in (0 : ℝ)..1,
            ‖(((1 / 2 - x : ℝ) : ℂ) *
              (P x * starRingEnd ℂ (P x)))‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ x in (0 : ℝ)..1, (1 / 2 : ℝ) * ‖P x‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on zero_le_one
          (hweighted.norm.intervalIntegrable 0 1)
          (hmajorant.intervalIntegrable 0 1)
        intro x hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          norm_mul, Complex.norm_conj]
        have hsaw : |1 / 2 - x| ≤ (1 / 2 : ℝ) := by
          rw [abs_le]
          constructor <;> linarith [hx.1, hx.2]
        calc
          |1 / 2 - x| * (‖P x‖ * ‖P x‖) ≤
              (1 / 2 : ℝ) * (‖P x‖ * ‖P x‖) :=
            mul_le_mul_of_nonneg_right hsaw
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = (1 / 2 : ℝ) * ‖P x‖ ^ 2 := by ring
      _ = (1 / 2 : ℝ) *
          ∫ x in (0 : ℝ)..1, ‖P x‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
      _ = (1 / 2 : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
        rw [show P = fourierPoly S a by rfl, finite_parseval]
  rw [finite_hilbert_identity, norm_mul]
  have hfactor : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos (by positivity)]
    norm_num
  rw [hfactor]
  calc
    (2 * π) *
        ‖∫ x in (0 : ℝ)..1,
          (((1 / 2 - x : ℝ) : ℂ) *
            (fourierPoly S a x * starRingEnd ℂ (fourierPoly S a x)))‖ ≤
        (2 * π) * ((1 / 2 : ℝ) * ∑ n ∈ S, ‖a n‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [P] using hintegral
      · positivity
    _ = π * ∑ n ∈ S, ‖a n‖ ^ 2 := by ring

end FiniteHilbert

end LeanProofs.IntegerPoints
