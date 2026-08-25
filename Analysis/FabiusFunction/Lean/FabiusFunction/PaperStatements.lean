import FabiusFunction.Basic
import FabiusFunction.AnalyticMoments
import FabiusFunction.BernoulliRecurrences
import FabiusFunction.DenominatorBound
import FabiusFunction.Differential
import FabiusFunction.DyadicAnalytic
import FabiusFunction.DyadicClosedForm
import FabiusFunction.DyadicCorrectness
import FabiusFunction.ExactInversePower
import FabiusFunction.Existence
import FabiusFunction.FourierAnalytic
import FabiusFunction.FourierProduct
import FabiusFunction.GlobalExtension
import FabiusFunction.GlobalDyadic
import FabiusFunction.HalfMomentDenominator
import FabiusFunction.MomentPowerSeries
import FabiusFunction.Monotonicity
import FabiusFunction.NormalizedEvenMoments
import FabiusFunction.NormalizedMoments
import FabiusFunction.Parity
import FabiusFunction.ScaleTranslation
import FabiusFunction.TaylorReduction
import FabiusFunction.TwoAdic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Results from *Arithmetic of the Fabius function*

This module formalizes every proved result in Juan Arias de Reyna,
*Arithmetic of the Fabius function*, arXiv:1702.06487v3.  It also records the
paper's Question 5, Definition 12, and Conjecture 16.  Every numbered result is
proved, as are the auxiliary existence, uniqueness, exact-evaluation, and
Fourier-transform results used by the development.

There are two deliberate corrections/clarifications:

* `fabius : ℝ → Set.Icc 0 1` is the bounded CDF requested for this project,
  while `extendedFabius : ℝ → ℝ` is the signed global function used by the
  paper outside `[0,1]`.
* Lemma 1 in the paper is false as printed.  Its proof requires the additional
  hypothesis `0 ≤ scale + order`; that hypothesis is included below.

Exact values, denominators, divisibility, and valuations live in `ℚ` or `ℕ`.
The bridge theorems below are the boundary between that arithmetic layer and
the analytic functions.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff Interval
open Finset MeasureTheory Set

namespace Fabius

noncomputable section

/-! ## The distinguished Fabius function -/

/-- The canonical bounded Fabius function `ℝ → [0,1]`. -/
noncomputable def fabius : BoundedFabius :=
  Classical.choose existsUnique_fabius

/-- The canonical function satisfies the defining Fabius properties. -/
theorem fabius_spec : IsFabius fabius :=
  (Classical.choose_spec existsUnique_fabius).1

/-- The assumed convention: the canonical bounded function is zero on `(-∞,0]`. -/
theorem fabius_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    fabiusReal fabius x = 0 :=
  fabius_spec.zero_of_nonpos x hx

/-- The clamped bounded function is one to the right of the unit interval. -/
theorem fabius_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    fabiusReal fabius x = 1 :=
  fabius_spec.one_of_one_le x hx

/-- The signed global extension of the canonical bounded function. -/
noncomputable def globalFabius : ℝ → ℝ :=
  extendedFabius fabius

/-! ## Analytic and exact-arithmetic bridges -/

/-- Normalization of Rvachev's function. -/
theorem rvachev_zero (F : BoundedFabius) (hF : IsFabius F) : rvachevUp F 0 = 1 :=
  rvachevUp_zero F hF

/-- Equations (5) and (7): the Fourier transform, sinc product, and moment series agree. -/
theorem rvachevFourier_eq_product_eq_series
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevFourier F z = rvachevFourierProduct z ∧
      rvachevFourierProduct z = rvachevMomentSeries z := by
  constructor
  · exact rvachevFourier_eq_product F hF z
  · exact (rvachevFourier_eq_product F hF z).symm.trans
      (rvachevFourier_eq_momentSeries F hF z)

/-- Equation (6): Fourier inversion for Rvachev's function. -/
theorem rvachev_fourier_inversion
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    (rvachevUp F x : ℂ) =
      ∫ t : ℝ, rvachevFourier F t *
        Complex.exp (2 * Real.pi * Complex.I * t * x) := by
  exact rvachev_fourier_inversion_analytic F hF x

/-- The Fourier transform of Rvachev's function is entire. -/
theorem rvachevFourier_differentiable (F : BoundedFabius) (hF : IsFabius F) :
    Differentiable ℂ (rvachevFourier F) := by
  exact rvachevFourier_differentiable_analytic F hF

/-- Equation (17): the analytic generating function has coefficients `d_n`. -/
theorem complexGeneratingFunction_eq_series
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z = halfMomentGeneratingSeries z := by
  exact complexGeneratingFunction_eq_series_formula F hF z

/-- The second equality in equation (20), expressed using the Fourier transform. -/
theorem complexGeneratingFunction_eq_fourier
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z =
      Complex.exp (z / 2) *
        rvachevFourier F (Complex.I * z / (4 * Real.pi)) := by
  exact complexGeneratingFunction_eq_fourier_analytic F hF z

/-- Equation (8): `moment n` is the `2n`-th moment of `rvachev`. -/
theorem moment_eq_integral (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (moment n : ℝ) = momentIntegral F n := by
  exact moment_eq_integral_formula F hF n

/-- Equation (21), whose integral form starts at `n = 1`. -/
theorem halfMoment_eq_integral (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    (halfMoment n : ℝ) = halfMomentIntegral F n := by
  exact halfMoment_eq_integral_formula F hF n hn

/-- Equations (21)--(22), connecting `d_n` to the bounded Fabius function. -/
theorem halfMoment_eq_fabius (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (halfMoment n : ℝ) =
      n.factorial * 2 ^ n.choose 2 * fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  exact halfMoment_eq_fabius_formula F hF n

/-- Equation (14), directly relating a half integral to a dyadic `up` value. -/
theorem halfIntegral_eq_rvachev_dyadic
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * ∫ t in (0 : ℝ)..1, t ^ (n - 1) * rvachevUp F t =
      n.factorial * 2 ^ n.choose 2 *
        rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹) := by
  exact halfIntegral_eq_rvachev_dyadic_formula F hF n hn

/-- Equation (15), specializing equation (14) to an even moment. -/
theorem moment_halfIntegral_eq_rvachev_dyadic
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (moment n : ℝ) / 2 =
        ∫ t in (0 : ℝ)..1, t ^ (2 * n) * rvachevUp F t ∧
    (∫ t in (0 : ℝ)..1, t ^ (2 * n) * rvachevUp F t) =
      (Nat.factorial (2 * n) : ℝ) * 2 ^ (2 * n + 1).choose 2 *
        rvachevUp F (1 - ((2 : ℝ) ^ (2 * n + 1))⁻¹) := by
  exact moment_halfIntegral_eq_rvachev_dyadic_formula F hF n

/-- Equation (16), the odd inverse-power value in terms of `F_n`. -/
theorem fabiusAtInverseTwoPow_odd (n : ℕ) :
    fabiusAtInverseTwoPow (2 * n + 1) =
      (momentNumerator n : ℚ) /
        ((2 : ℚ) ^ (2 * n + 1).choose 2 * 2 * Nat.factorial (2 * n) *
          oddDoubleFactorial (n + 1) * evenMersenneProduct n) := by
  exact fabiusAtInverseTwoPow_odd_formula n

/-- Equation (25), the general inverse-power value in terms of `G_n`. -/
theorem fabiusAtInverseTwoPow_eq_halfMomentNumerator (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (halfMomentNumerator n : ℚ) /
        ((2 : ℚ) ^ n.choose 2 * n.factorial * (n + 1).factorial *
          mersenneProduct n) := by
  exact fabiusAtInverseTwoPow_eq_halfMomentNumerator_formula n

/-- Equation (26) and its natural divisibility consequence. -/
theorem halfMomentNumerator_odd_index (n : ℕ) :
    (halfMomentNumerator (2 * n + 1) : ℚ) / (2 * n + 1) =
      ((2 ^ n * (n + 1).factorial * momentNumerator n *
        oddMersenneProduct n : ℕ) : ℚ) ∧
    (2 * n + 1) * momentNumerator n ∣ halfMomentNumerator (2 * n + 1) := by
  exact halfMomentNumerator_odd_index_formula n

/-! ## Correctness specifications for the executable dyadic evaluator -/

/-- Equation (32) on its full `[0,2]` range, using the signed extension. -/
theorem fabiusDyadic_cast_extended (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) :
    (fabiusDyadic n a : ℝ) =
      extendedFabius F (a / (2 : ℝ) ^ n) := by
  exact fabiusDyadic_cast_extended_formula F hF n a ha

/-- The total signed-numerator evaluator computes the bounded Fabius function. -/
theorem fabiusDyadicValue_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (a : ℤ) :
    (fabiusDyadicValue n a : ℝ) =
      fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) := by
  by_cases ha : a ≤ 0
  · rw [fabiusDyadicValue_of_nonpos n a ha]
    norm_num
    apply (hF.zero_of_nonpos _ ?_).symm
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ha) (by positivity)
  · have hapos : 0 < a := lt_of_not_ge ha
    by_cases hge : (2 ^ n : ℤ) ≤ a
    · rw [fabiusDyadicValue_of_ge n a hge]
      norm_num
      apply (hF.one_of_one_le _ ?_).symm
      rw [le_div_iff₀' (by positivity : (0 : ℝ) < 2 ^ n)]
      norm_num at hge ⊢
      exact_mod_cast hge
    · rw [fabiusDyadicValue, if_neg ha]
      have htoNat : (a.toNat : ℤ) = a := Int.toNat_of_nonneg hapos.le
      have hbound : a.toNat ≤ 2 ^ n := by
        exact ((Int.toNat_lt hapos.le).2 (lt_of_not_ge hge)).le
      rw [fabiusDyadicUnit_eq_fabiusDyadic n a.toNat hbound,
        fabiusDyadic_cast F hF n a.toNat hbound]
      congr 1
      rw [show (a.toNat : ℝ) = (a : ℝ) by exact_mod_cast htoNat]

/-- A successful rational-input evaluation has the correct bounded value. -/
theorem evalFabiusDyadic_eq_some_correct (F : BoundedFabius) (hF : IsFabius F)
    (x value : ℚ) (hvalue : evalFabiusDyadic x = some value) :
    (value : ℝ) = fabiusReal F (x : ℝ) := by
  unfold evalFabiusDyadic at hvalue
  split at hvalue
  · simp at hvalue
  · rename_i exponent hexponent
    injection hvalue with hvalue
    subst value
    have hden : x.den = 2 ^ exponent := by
      unfold dyadicExponent? at hexponent
      dsimp only at hexponent
      split at hexponent
      · rename_i h
        injection hexponent with he
        simpa [he] using h
      · simp at hexponent
    rw [fabiusDyadicValue_cast F hF]
    congr 1
    rw [Rat.cast_def, hden]
    norm_num

/-- A successful rational-input evaluation has the correct global value. -/
theorem evalExtendedFabiusDyadic_eq_some_correct
    (F : BoundedFabius) (hF : IsFabius F)
    (x value : ℚ) (hvalue : evalExtendedFabiusDyadic x = some value) :
    (value : ℝ) = extendedFabius F (x : ℝ) := by
  unfold evalExtendedFabiusDyadic at hvalue
  split at hvalue
  · simp at hvalue
  · rename_i exponent hexponent
    injection hvalue with hvalue
    subst value
    have hden : x.den = 2 ^ exponent := by
      unfold dyadicExponent? at hexponent
      dsimp only at hexponent
      split at hexponent
      · rename_i h
        injection hexponent with he
        simpa [he] using h
      · simp at hexponent
    rw [extendedFabiusDyadicValue_cast F hF]
    congr 1
    rw [Rat.cast_def, hden]
    norm_num

/--
Every dyadic rational has an explicitly computed rational value equal to the
bounded analytic Fabius function.
-/
theorem evalFabiusDyadic_complete_correct
    (F : BoundedFabius) (hF : IsFabius F) (x : ℚ)
    (hx : IsDyadicRational x) :
    ∃ value : ℚ,
      evalFabiusDyadic x = some value ∧
        (value : ℝ) = fabiusReal F (x : ℝ) := by
  obtain ⟨exponent, hexponent⟩ := (dyadicExponent?_exists_iff x).2 hx
  let value := fabiusDyadicValue exponent x.num
  have hvalue : evalFabiusDyadic x = some value := by
    simp [evalFabiusDyadic, hexponent, value]
  exact ⟨value, hvalue, evalFabiusDyadic_eq_some_correct F hF x value hvalue⟩

/-- The Fabius-grid and Rvachev-grid descriptions of Definition 12 agree. -/
theorem dyadicDenominator_eq_fabiusDyadicDenominator (n : ℕ) :
    dyadicDenominator n = fabiusDyadicDenominator n := by
  cases n with
  | zero => simp [dyadicDenominator, fabiusDyadicDenominator,
      oddDyadicNumerators]
  | succ n =>
      apply Nat.dvd_antisymm
      · unfold dyadicDenominator fabiusDyadicDenominator
        apply Finset.lcm_dvd
        intro a ha
        have ha_filter := (mem_filter.mp (show
          a ∈ (Finset.Icc 1 (2 ^ (n + 1) - 1)).filter Odd by
            simpa [oddDyadicNumerators] using ha))
        have ha_bounds := Finset.mem_Icc.mp ha_filter.1
        have hascale : a ≤ 2 ^ (n + 1) := by omega
        have hreflect : 2 ^ (n + 1) - a ∈ oddDyadicNumerators (n + 1) :=
          oddDyadicNumerators_reflect_mem (n + 1) a (by omega) ha
        rw [rvachevDyadic, if_pos, Rat.den_abs_eq_den]
        · exact Finset.dvd_lcm hreflect
        · simpa using hascale
      · unfold dyadicDenominator fabiusDyadicDenominator
        apply Finset.lcm_dvd
        intro a ha
        have ha_filter := (mem_filter.mp (show
          a ∈ (Finset.Icc 1 (2 ^ (n + 1) - 1)).filter Odd by
            simpa [oddDyadicNumerators] using ha))
        have ha_bounds := Finset.mem_Icc.mp ha_filter.1
        let b := 2 ^ (n + 1) - a
        have hbmem : b ∈ oddDyadicNumerators (n + 1) :=
          oddDyadicNumerators_reflect_mem (n + 1) a (by omega) ha
        have hbscale : b ≤ 2 ^ (n + 1) := by
          dsimp [b]
          omega
        have hba : 2 ^ (n + 1) - b = a := by
          dsimp [b]
          omega
        have hdvd := Finset.dvd_lcm (f := fun c : ℕ =>
          (rvachevDyadic (n + 1) c).den) hbmem
        rw [rvachevDyadic, if_pos, Rat.den_abs_eq_den] at hdvd
        · simpa [b, hba] using hdvd
        · simpa using hbscale

/-- The exact `R_n` is the paper's analytic expression after coercion to `ℝ`. -/
theorem reshetnikov_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    (reshetnikov n : ℝ) =
      (2 : ℝ) ^ (n - 1).choose 2 * (Nat.factorial (2 * n) : ℝ) *
        fabiusReal F (((2 : ℝ) ^ n)⁻¹) * evenMersenneProduct (n / 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold reshetnikov fabiusAtInverseTwoPow
  push_cast
  rw [fabiusDyadic_cast F hF (1 + m) 1 Nat.one_le_two_pow]
  congr 3
  norm_num

/-! ## Numbered results -/

/-- Proposition 1: recurrence and natural normalization of the moments `c_n`. -/
theorem proposition_one :
    moment 0 = 1 ∧
    (∀ n : ℕ, 1 ≤ n →
      (((2 * n + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * n) - 1) * moment n =
        (∑ k ∈ range n,
          (Nat.choose (2 * n + 1) (2 * k) : ℚ) * moment k))) ∧
    (∀ n : ℕ,
      moment n =
        (momentNumerator n : ℚ) /
          ((oddDoubleFactorial (n + 1) * evenMersenneProduct n : ℕ) : ℚ)) := by
  refine ⟨moment_zero, ?_, moment_eq_momentNumerator_div⟩
  intro n hn
  have h := moment_original_recurrence n
  rw [sum_range_succ] at h
  have hchoose : (2 * n + 1).choose (2 * n) = 2 * n + 1 := by
    exact Nat.choose_succ_self_right (2 * n)
  rw [hchoose] at h
  push_cast at h
  push_cast
  linear_combination h

/-- Proposition 2: the functional equation for the entire generating function. -/
theorem proposition_two (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F (2 * z) =
      complexExpm1Div z * complexGeneratingFunction F z := by
  exact proposition_two_formula F hF z

/-- The real restriction of Proposition 2. -/
theorem proposition_two_real (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    generatingFunction F (2 * x) = expm1Div x * generatingFunction F x := by
  exact proposition_two_real_formula F hF x

/-- Proposition 3: the half moments in terms of the even moments. -/
theorem proposition_three (n : ℕ) :
    halfMoment n =
      (∑ k ∈ range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℚ) * moment k) / (2 : ℚ) ^ n := by
  exact halfMoment_eq_evenMomentSum n

/-- Proposition 4: the natural normalization `G_n` of the half moments. -/
theorem proposition_four (n : ℕ) :
    halfMoment n =
      (halfMomentNumerator n : ℚ) /
        (((n + 1).factorial * mersenneProduct n : ℕ) : ℚ) := by
  exact halfMoment_eq_halfMomentNumerator n

/-- Question 5 (Reshetnikov), subsequently answered by Theorem 9. -/
def reshetnikovQuestion : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsNatural (reshetnikov n)

/-- Proposition 6: `R_n` in terms of `d_n`. -/
theorem proposition_six (n : ℕ) (hn : 1 ≤ n) :
    reshetnikov n =
      2 * halfMoment n * oddDoubleFactorial n * evenMersenneProduct (n / 2) := by
  rw [reshetnikov, fabiusAtInverseTwoPow_eq_halfMoment,
    halfMomentFabiusValue, factorial_two_mul_eq]
  have hexp : (n - 1).choose 2 + n = n.choose 2 + 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 1 + m - 1 = m by omega]
    rw [show 1 + m = m + 1 by omega]
    rw [show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
    simp [Nat.choose_one_right]
    omega
  push_cast
  field_simp
  rw [← pow_add, hexp, pow_succ]
  ring

/-- Theorem 7: the exact odd-index formula, hence divisibility by `F_n`. -/
theorem theorem_seven (n : ℕ) :
    reshetnikov (2 * n + 1) =
      (momentNumerator n : ℚ) *
        (∏ j ∈ Icc n (2 * n), ((2 * j + 1 : ℕ) : ℚ)) ∧
    IsNatural (reshetnikov (2 * n + 1)) ∧
    (∃ m : ℕ,
      reshetnikov (2 * n + 1) = (momentNumerator n * m : ℕ)) := by
  let m : ℕ := ∏ j ∈ Icc n (2 * n), (2 * j + 1)
  have hodd := oddDoubleFactorial_mul_Icc n
  have hoddRat := congrArg (fun z : ℕ => (z : ℚ)) hodd
  push_cast at hoddRat
  have hoddPos : 0 < oddDoubleFactorial (n + 1) := by
    unfold oddDoubleFactorial
    apply Finset.prod_pos
    intro j hj
    omega
  have hevenPos : 0 < evenMersenneProduct n := by
    unfold evenMersenneProduct
    apply Finset.prod_pos
    intro j hj
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))
  have hden :
      (((oddDoubleFactorial (n + 1) * evenMersenneProduct n : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hoddPos hevenPos))
  have hvalue :
      reshetnikov (2 * n + 1) = (momentNumerator n : ℚ) * (m : ℚ) := by
    rw [proposition_six (2 * n + 1) (by omega),
      halfMoment_odd_eq_moment, moment_eq_momentNumerator_div]
    rw [show (2 * n + 1) / 2 = n by omega]
    field_simp [hden]
    dsimp [m]
    push_cast
    linear_combination
      (momentNumerator n : ℚ) * (evenMersenneProduct n : ℚ) * hoddRat
  refine ⟨?_, ?_, ?_⟩
  · simpa [m] using hvalue
  · refine ⟨momentNumerator n * m, ?_⟩
    rw [hvalue]
    push_cast
    rfl
  · exact ⟨m, by simpa using hvalue⟩

/-- Equation (30), the exact finite sum for the even Reshetnikov numbers. -/
theorem reshetnikov_even_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    reshetnikov (2 * n) =
      ∑ k : Fin (n + 1),
        (2 * (momentNumerator k.val : ℚ) * Nat.choose (2 * n) (2 * k.val) *
          oddFactorProduct (k.val + 1) (2 * n) *
          (∏ ell ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * ell) - 1))) /
            (2 : ℚ) ^ (2 * n) := by
  rw [proposition_six (2 * n) (by omega)]
  rw [show (2 * n) / 2 = n by omega]
  rw [halfMoment_eq_evenMomentSum]
  rw [show (2 * n) / 2 = n by omega]
  rw [Fin.sum_univ_eq_sum_range
    (fun k =>
      (2 * (momentNumerator k : ℚ) * Nat.choose (2 * n) (2 * k) *
        oddFactorProduct (k + 1) (2 * n) *
        (∏ ell ∈ Ico (k + 1) (n + 1), (2 ^ (2 * ell) - 1))) /
          (2 : ℚ) ^ (2 * n)) (n + 1)]
  rw [Finset.sum_div]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [moment_eq_momentNumerator_div]
  have hk_le : k ≤ n := by simpa using hk
  have hodd := oddDoubleFactorial_mul_interval (k + 1) (2 * n) (by omega)
  have heven := evenMersenneProduct_mul_interval k n hk_le
  have hdenPos :
      0 < oddDoubleFactorial (k + 1) * evenMersenneProduct k := by
    unfold oddDoubleFactorial evenMersenneProduct
    apply Nat.mul_pos
    · apply Finset.prod_pos
      intro j hj
      omega
    · apply Finset.prod_pos
      intro j hj
      exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))
  have hden :
      (((oddDoubleFactorial (k + 1) * evenMersenneProduct k : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdenPos)
  have hoddRat := congrArg (fun z : ℕ => (z : ℚ)) hodd
  have hevenRat := congrArg (fun z : ℕ => (z : ℚ)) heven
  push_cast at hoddRat hevenRat
  simp_rw [mersenneFactor_cast] at hevenRat
  field_simp [hden]
  push_cast
  rw [← hoddRat, ← hevenRat]
  ring

/-- Proposition 8: the even-index formula and its power-of-two denominator bound. -/
theorem proposition_eight (n : ℕ) (hn : 1 ≤ n) :
    reshetnikov (2 * n) =
      ∑ k : Fin (n + 1),
        (2 * (momentNumerator k.val : ℚ) * Nat.choose (2 * n) (2 * k.val) *
          oddFactorProduct (k.val + 1) (2 * n) *
          (∏ ell ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * ell) - 1))) /
            (2 : ℚ) ^ (2 * n) ∧
    (reshetnikov (2 * n)).den ∣ 2 ^ (2 * n) := by
  refine ⟨reshetnikov_even_eq_sum n hn, ?_⟩
  let summand : Fin (n + 1) → ℕ := fun k =>
    2 * momentNumerator k.val * Nat.choose (2 * n) (2 * k.val) *
      oddFactorProduct (k.val + 1) (2 * n) *
      (∏ ell ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * ell) - 1))
  let numerator : ℕ := ∑ k, summand k
  have hcast :
      (numerator : ℚ) =
        ∑ k : Fin (n + 1),
          2 * (momentNumerator k.val : ℚ) * Nat.choose (2 * n) (2 * k.val) *
            oddFactorProduct (k.val + 1) (2 * n) *
            (∏ ell ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * ell) - 1)) := by
    dsimp [numerator, summand]
    push_cast
    simp_rw [mersenneFactor_cast]
  rw [reshetnikov_even_eq_sum n hn]
  rw [← Finset.sum_div, ← hcast]
  have hpowCast : (((2 ^ (2 * n) : ℕ) : ℚ)) = (2 : ℚ) ^ (2 * n) := by
    norm_num
  rw [← hpowCast]
  exact rat_den_dvd_nat_div numerator (2 ^ (2 * n))

/-- Theorem 9: Reshetnikov's numbers are natural numbers. -/
theorem theorem_nine (n : ℕ) (hn : 1 ≤ n) :
    IsNatural (reshetnikov n) := by
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨m, hm⟩ := heven
    have hnEq : n = 2 * m := by omega
    subst n
    rw [hnEq]
    have hmpos : 1 ≤ m := by omega
    have hdenDvd : (reshetnikov (2 * m)).den ∣ 2 ^ (2 * m) :=
      (proposition_eight m hmpos).2
    have hdenOdd : Odd (reshetnikov (2 * m)).den := by
      rw [proposition_six (2 * m) (by omega)]
      rw [show (2 * m) / 2 = m by omega]
      have hvalue :
          2 * halfMoment (2 * m) * (oddDoubleFactorial (2 * m) : ℚ) *
              (evenMersenneProduct m : ℚ) =
            ((oddDoubleFactorial (2 * m) * evenMersenneProduct m : ℕ) : ℚ) *
              (2 * halfMoment (2 * m)) := by
        push_cast
        ring
      rw [hvalue]
      exact rat_den_mul_nat_odd
        (oddDoubleFactorial (2 * m) * evenMersenneProduct m)
        (2 * halfMoment (2 * m))
        (two_mul_halfMoment_den_odd (2 * m))
    have hcoprime :
        (reshetnikov (2 * m)).den.Coprime (2 ^ (2 * m)) :=
      (Nat.coprime_two_right.mpr hdenOdd).pow_right (2 * m)
    have hden : (reshetnikov (2 * m)).den = 1 :=
      hcoprime.eq_one_of_dvd hdenDvd
    have hoddPos : 0 < oddDoubleFactorial (2 * m) := by
      unfold oddDoubleFactorial
      apply Finset.prod_pos
      intro j hj
      omega
    have hevenPos : 0 < evenMersenneProduct m := by
      unfold evenMersenneProduct
      apply Finset.prod_pos
      intro j hj
      exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))
    have hvaluePos : 0 < reshetnikov (2 * m) := by
      rw [proposition_six (2 * m) (by omega)]
      rw [show (2 * m) / 2 = m by omega]
      apply mul_pos
      · apply mul_pos
        · exact mul_pos (by norm_num) (halfMoment_pos (2 * m))
        · exact_mod_cast hoddPos
      · exact_mod_cast hevenPos
    have hnumNonneg : 0 ≤ (reshetnikov (2 * m)).num :=
      Rat.num_nonneg.mpr (le_of_lt hvaluePos)
    refine ⟨(reshetnikov (2 * m)).num.natAbs, ?_⟩
    calc
      reshetnikov (2 * m) = ((reshetnikov (2 * m)).num : ℚ) :=
        (Rat.coe_int_num_of_den_eq_one hden).symm
      _ = (((reshetnikov (2 * m)).num.natAbs : ℕ) : ℚ) := by
        have hnumEq :
            (reshetnikov (2 * m)).num =
              Int.ofNat (reshetnikov (2 * m)).num.natAbs :=
          (Int.natAbs_of_nonneg hnumNonneg).symm
        simpa using congrArg (fun z : ℤ => (z : ℚ)) hnumEq
  · obtain ⟨m, hm⟩ := hodd
    have hnEq : n = 2 * m + 1 := by omega
    subst n
    exact (theorem_seven m).2.1

/--
Lemma 1, with the missing hypothesis from the printed paper restored.
Without `horder`, the statement is false when `scale` is negative.
-/
theorem lemma_one (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (scale : ℤ) (order : ℕ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ scale ≤ x)
    (hhi : x < (2 : ℝ) ^ (scale + 1))
    (horder : (0 : ℤ) ≤ scale + order) :
    (∫ t in (2 : ℝ) ^ scale..x,
        (x - t) ^ order * iteratedDeriv (order + 1) (extendedFabius F) t) =
      -(∫ t in 0..(x - (2 : ℝ) ^ scale),
        (x - (2 : ℝ) ^ scale - t) ^ order *
          iteratedDeriv (order + 1) (extendedFabius F) t) := by
  exact taylorRemainder_translate F hF x scale order hx hlo hhi horder

/-- Proposition 10: the recursive evaluation formula for the signed extension. -/
theorem proposition_ten (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) (n : ℤ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ (-n) ≤ x)
    (hhi : x < (2 : ℝ) ^ (-n + 1)) :
    let y := x - (2 : ℝ) ^ (-n)
    extendedFabius F x = -extendedFabius F y +
      if 0 ≤ n then fabiusReductionSum n.toNat y else 0 := by
  exact extendedFabius_reduction F hF x n hx hlo hhi

/-
Definition 12 is `dyadicDenominator` in `Arithmetic.lean`: the LCM of the
reduced denominators on the positive odd level-`n` dyadic grid.
-/

/-- Theorem 13: a common integral scaling of all level-`n` dyadic values.
The positivity hypothesis mirrors the paper; the underlying exact scaling
theorem is valid at level zero as well. -/
theorem theorem_thirteen (n : ℕ) (hn : 1 ≤ n) (a : ℤ)
    (haLower : -((2 ^ n : ℕ) : ℤ) < a)
    (haUpper : a < ((2 ^ n : ℕ) : ℤ)) :
    IsNatural (rvachevDyadic n a * denominatorBound n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have habs : a.natAbs ≤ 2 ^ (1 + m) := by
    rcases Int.natAbs_eq a with h | h
    · omega
    · omega
  exact rvachevDyadic_mul_denominatorBound_isNatural (1 + m) a habs

/-- The common-denominator formulation following Theorem 13.  Positivity is
retained to mirror the paper, although the denominator bound holds at every
natural level. -/
theorem theorem_thirteen_denominator_bound (n : ℕ) (hn : 1 ≤ n) :
    dyadicDenominator n ∣ denominatorBound n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact dyadicDenominator_dvd_denominatorBound (1 + m)

/-- Proposition 15: the denominator at `2⁻ⁿ` divides the common denominator. -/
theorem proposition_fifteen (n : ℕ) :
    (halfMomentFabiusValue n).den ∣ dyadicDenominator n := by
  rw [dyadicDenominator_eq_fabiusDyadicDenominator]
  by_cases hn : n = 0
  · subst n
    norm_num [halfMomentFabiusValue, fabiusDyadicDenominator]
  · rw [← fabiusAtInverseTwoPow_eq_halfMoment]
    unfold fabiusAtInverseTwoPow fabiusDyadicDenominator
    apply Finset.dvd_lcm
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpow : 1 < 2 ^ n := one_lt_pow₀ (by omega) hn
    have hone : 1 ≤ 2 ^ n - 1 := by omega
    simp [oddDyadicNumerators, hone]

/--
Conjecture 16.  Natural divisibility is expressed through an explicit natural
quotient, rather than `∣` in `ℚ` (where divisibility would be trivial).
-/
def conjecture_sixteen : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    normalizedDyadicDenominator (2 * n) =
      normalizedDyadicDenominator (2 * n + 1)) ∧
  (∀ n : ℕ, 2 ≤ n →
    conjecturalK n = normalizedDyadicDenominator (2 * n - 2)) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∃ q : ℕ, conjecturalK n = (2 * (2 * n - 1).factorial * q : ℕ)) ∧
  (∀ n : ℕ, 1 ≤ n → IsOddNatural (conjecturalH n))

/-- Theorem 17: Lucas's theorem in the digit-product form used by the paper. -/
theorem theorem_seventeen (p n k a : ℕ) (hp : p.Prime)
    (hn : n < p ^ (a + 1)) (hk : k < p ^ (a + 1)) :
    Nat.ModEq p (Nat.choose n k)
      (∏ i ∈ range (a + 1),
        Nat.choose (n / p ^ i % p) (k / p ^ i % p)) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact Choose.lucas_theorem_nat hn hk

/-- Proposition 18: counts of the odd binomial coefficients in the two ranges.
The positivity hypothesis follows the paper's indexing; the underlying count
also holds at `n = 0`. -/
theorem proposition_eighteen (n : ℕ) (hn : 1 ≤ n) :
    ((range (n + 1)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) (2 * k)))).card =
        2 ^ binaryWeight n ∧
    ((range (2 * n + 2)).filter
      (fun k => Odd (Nat.choose (2 * n + 1) k))).card =
        2 ^ (binaryWeight n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact odd_binomial_coefficient_counts (1 + m)

/-- Proposition 19: every natural moment numerator `F_n` is odd. -/
theorem proposition_nineteen (n : ℕ) :
    Odd (momentNumerator n) := by
  exact momentNumerator_odd n

/-- Theorem 20: the numerator and denominator of `2 d_n` are odd. -/
theorem theorem_twenty (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (2 * halfMoment n) = 0 ∧
      Odd (2 * halfMoment n).num.natAbs ∧ Odd (2 * halfMoment n).den := by
  exact two_mul_halfMoment_padicVal_two_and_odd n hn

/-- Theorem 21: oddness of `R_n` and the exact dyadic valuation. -/
theorem theorem_twenty_one (n : ℕ) (hn : 1 ≤ n) :
    IsOddNatural (reshetnikov n) ∧
    padicValRat 2 (fabiusAtInverseTwoPow n) =
      -(n.choose 2 : ℤ) - 1 - padicValRat 2 (n.factorial : ℚ) := by
  refine ⟨?_, fabiusAtInverseTwoPow_padicVal_two n hn⟩
  have htwo := (theorem_twenty n hn).2
  have hfirst := odd_num_den_mul_nat (oddDoubleFactorial n) htwo
    (odd_oddDoubleFactorial n)
  have hsecond := odd_num_den_mul_nat (evenMersenneProduct (n / 2)) hfirst
    (odd_evenMersenneProduct (n / 2))
  have hRodd :
      Odd (reshetnikov n).num.natAbs ∧ Odd (reshetnikov n).den := by
    rw [proposition_six n hn]
    simpa [mul_assoc] using hsecond
  apply isOddNatural_of_isNatural_of_odd_num _ hRodd.1
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 1 ≤ m := by omega
    have hdenDvd := (proposition_eight m hm).2
    have hdenOne := odd_eq_one_of_dvd_two_pow hRodd.2 hdenDvd
    apply isNatural_of_den_eq_one_of_nonneg hdenOne
    rw [(proposition_eight m hm).1]
    apply Finset.sum_nonneg
    intro k hk
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · apply Finset.prod_nonneg
        intro ell hell
        exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    · positivity
  · exact (theorem_seven m).2.1

/-- Proposition 22: the Bernoulli recurrences for `c_n` and `d_n`. -/
theorem proposition_twenty_two_initial : moment 0 = 1 ∧ halfMoment 0 = 1 := by
  simp

theorem proposition_twenty_two (n : ℕ) (hn : 1 ≤ n) :
    moment n =
      (∑ k ∈ Icc 1 n,
        (2 : ℚ) ^ (2 * n - 2 * k) * ((2 : ℚ) ^ (2 * k) - 2) *
          Nat.choose (2 * n) (2 * k) * bernoulli (2 * k) * moment (n - k)) /
        ((2 : ℚ) ^ (2 * n) - 1) ∧
    halfMoment n =
      ((n : ℚ) * (2 : ℚ) ^ n / (4 * ((2 : ℚ) ^ n - 1))) *
          halfMoment (n - 1) -
        (∑ k ∈ Icc 1 (n / 2),
          (Nat.choose n (2 * k) : ℚ) * (2 : ℚ) ^ (n - 2 * k) *
            bernoulli (2 * k) * halfMoment (n - 2 * k)) /
          ((2 : ℚ) ^ n - 1) := by
  exact proposition_twenty_two_formula n hn

end

end Fabius
