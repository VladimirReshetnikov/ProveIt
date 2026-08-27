import FabiusFunction.Differential
import FabiusFunction.DyadicClosedForm
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Analytic correctness of exact dyadic Fabius evaluation

The bounded Fabius differential equation yields a finite Taylor recurrence on
each dyadic scale. Endpoint compatibility determines its inverse-power values,
and comparison with the exact closed-form recurrence proves that the rational
dyadic evaluator computes the analytic function.  The final API includes the
exact right endpoint of every unit dyadic grid, a direct real-cast identity for
the inverse-power table, and total analytic correctness for the clamped
natural-numerator evaluator.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

noncomputable section

private def inverseTwoPowReal (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

private def analyticInverseValue (F : BoundedFabius) (n : ℕ) : ℝ :=
  fabiusReal F (inverseTwoPowReal n)

private def analyticTaylorSum (F : BoundedFabius) (m : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range (m + 1),
    (2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (m - k) *
      y ^ k / k.factorial

@[simp] private lemma inverseTwoPowReal_zero : inverseTwoPowReal 0 = 1 := by
  simp [inverseTwoPowReal]

private lemma two_mul_inverseTwoPowReal_succ (n : ℕ) :
    2 * inverseTwoPowReal (n + 1) = inverseTwoPowReal n := by
  simp only [inverseTwoPowReal, pow_succ]
  field_simp

private lemma inverseTwoPowReal_pos (n : ℕ) : 0 < inverseTwoPowReal n := by
  simp only [inverseTwoPowReal]
  positivity

private lemma inverseTwoPowReal_le_half (n : ℕ) (hn : 1 ≤ n) :
    inverseTwoPowReal n ≤ 1 / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [inverseTwoPowReal, pow_add, pow_one]
  have hp : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hden : (2 : ℝ) ≤ 2 * 2 ^ m := by nlinarith
  simpa [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hden

@[simp] private lemma analyticTaylorSum_zero (F : BoundedFabius) (m : ℕ) :
    analyticTaylorSum F m 0 = analyticInverseValue F m := by
  rw [analyticTaylorSum]
  rw [Finset.sum_range_succ']
  simp

private lemma analyticTaylorSum_derivative_identity
    (F : BoundedFabius) (m : ℕ) (y : ℝ) :
    HasDerivAt (analyticTaylorSum F (m + 1))
      (2 * analyticTaylorSum F m (2 * y)) y := by
  have hderiv : HasDerivAt (analyticTaylorSum F (m + 1))
      (∑ k ∈ range (m + 1 + 1),
        ((2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (m + 1 - k) /
          k.factorial) * ((k : ℝ) * y ^ (k - 1))) y := by
    let c : ℕ → ℝ := fun k =>
      (2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (m + 1 - k) /
        k.factorial
    have h := HasDerivAt.sum (u := range (m + 1 + 1))
      (fun k _hk => (hasDerivAt_pow k y).const_mul (c k))
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with z
      unfold analyticTaylorSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c]
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c]
  convert hderiv using 1
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  rw [analyticTaylorSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hfac : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
    rw [Nat.factorial_succ]
    norm_num
  have hchoose := choose_add_two_two j
  rw [show m + 1 - (j + 1) = m - j by omega, hchoose, pow_add,
    pow_succ, mul_pow, hfac]
  have hjfac : (j.factorial : ℝ) ≠ 0 := by positivity
  have hjsucc : ((j : ℝ) + 1) ≠ 0 := by positivity
  rw [show j + 1 - 1 = j by omega]
  push_cast
  field_simp

private lemma analyticTaylorSum_continuous (F : BoundedFabius) (m : ℕ) :
    Continuous (analyticTaylorSum F m) := by
  unfold analyticTaylorSum
  fun_prop

private lemma analytic_scale_recurrence_one
    (F : BoundedFabius) (hF : IsFabius F) (y : ℝ)
    (hy0 : 0 ≤ y) (hy : y ≤ inverseTwoPowReal 1) :
    fabiusReal F (inverseTwoPowReal 1 + y) + fabiusReal F y =
      analyticTaylorSum F 1 y := by
  let lhs : ℝ → ℝ := fun z =>
    fabiusReal F (inverseTwoPowReal 1 + z) + fabiusReal F z
  let rhs : ℝ → ℝ := analyticTaylorSum F 1
  have hlhsCont : Continuous lhs := by
    dsimp only [lhs]
    exact ((hF.contDiff.continuous.comp
      (continuous_const.add continuous_id))).add hF.contDiff.continuous
  have hrhsCont : Continuous rhs := analyticTaylorSum_continuous F 1
  have hderivLhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal 1),
      HasDerivWithinAt lhs 2 (Ici z) z := by
    intro z hz
    have hzhalf : z ∈ Icc (0 : ℝ) (1 / 2) := by
      constructor
      · exact hz.1
      · simpa [inverseTwoPowReal] using hz.2.le
    have htlow : 1 / 2 ≤ inverseTwoPowReal 1 + z := by
      norm_num [inverseTwoPowReal]
      exact hz.1
    have hhigh := fabius_hasDerivAt_reflected_of_half_le F hF htlow
    have hlow := hF.hasDerivAt z hzhalf
    have hsym := hF.symmetry (2 * z)
      ⟨mul_nonneg (by norm_num) hz.1, by linarith [hzhalf.2]⟩
    have hhighComp := hhigh.comp z ((hasDerivAt_const z (inverseTwoPowReal 1)).add
      (hasDerivAt_id z))
    have hsum := hhighComp.fun_add hlow
    have hsum' : HasDerivAt lhs 2 z := by
      have hargEq : 2 - 2 * (inverseTwoPowReal 1 + z) = 1 - 2 * z := by
        norm_num [inverseTwoPowReal]
        ring
      have hcoef :
          2 * fabiusReal F (2 - 2 * (inverseTwoPowReal 1 + z)) * (0 + 1) +
              2 * fabiusReal F (2 * z) = 2 := by
        rw [hargEq, hsym]
        ring
      have hsum' := hsum.congr_deriv hcoef
      simpa only [lhs, Function.comp_apply, Pi.add_apply] using hsum'
    exact hsum'.hasDerivWithinAt.mono (by intro x hx; exact hx)
  have hderivRhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal 1),
      HasDerivWithinAt rhs 2 (Ici z) z := by
    intro z hz
    have h := analyticTaylorSum_derivative_identity F 0 z
    have h' : HasDerivAt rhs 2 z := by
      convert h using 1
      simp [analyticTaylorSum, analyticInverseValue, hF.one_of_one_le]
    exact h'.hasDerivWithinAt.mono (by intro x hx; exact hx)
  have hhalf : fabiusReal F (1 / 2) = 1 / 2 := by
    have hs := hF.symmetry (1 / 2) (by constructor <;> norm_num)
    norm_num at hs ⊢
    linarith
  have hzero : lhs 0 = rhs 0 := by
    dsimp only [lhs, rhs]
    rw [analyticTaylorSum_zero]
    simp only [analyticInverseValue]
    rw [hF.zero_of_nonpos 0 le_rfl]
    norm_num [inverseTwoPowReal] at hhalf ⊢
  exact eq_of_has_deriv_right_eq hderivLhs hderivRhs
    hlhsCont.continuousOn hrhsCont.continuousOn hzero y ⟨hy0, hy⟩

private lemma analytic_scale_recurrence_succ
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) (hm : 1 ≤ m)
    (ih : ∀ y : ℝ, 0 ≤ y → y ≤ inverseTwoPowReal m →
      fabiusReal F (inverseTwoPowReal m + y) + fabiusReal F y =
        analyticTaylorSum F m y)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ inverseTwoPowReal (m + 1)) :
    fabiusReal F (inverseTwoPowReal (m + 1) + y) + fabiusReal F y =
      analyticTaylorSum F (m + 1) y := by
  let lhs : ℝ → ℝ := fun z =>
    fabiusReal F (inverseTwoPowReal (m + 1) + z) + fabiusReal F z
  let rhs : ℝ → ℝ := analyticTaylorSum F (m + 1)
  have hlhsCont : Continuous lhs := by
    dsimp only [lhs]
    exact ((hF.contDiff.continuous.comp
      (continuous_const.add continuous_id))).add hF.contDiff.continuous
  have hrhsCont : Continuous rhs := analyticTaylorSum_continuous F (m + 1)
  have hderivLhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal (m + 1)),
      HasDerivWithinAt lhs (2 * analyticTaylorSum F m (2 * z)) (Ici z) z := by
    intro z hz
    have hzscaled : 2 * z ≤ inverseTwoPowReal m := by
      rw [← two_mul_inverseTwoPowReal_succ m]
      nlinarith [hz.2.le]
    have hinvhalf := inverseTwoPowReal_le_half m hm
    have hzhalf : z ∈ Icc (0 : ℝ) (1 / 2) := by
      constructor
      · exact hz.1
      · have hzle : z ≤ inverseTwoPowReal (m + 1) := hz.2.le
        exact hzle.trans (inverseTwoPowReal_le_half (m + 1) (by omega))
    have hsumhalf : inverseTwoPowReal (m + 1) + z ≤ 1 / 2 := by
      have hdouble : inverseTwoPowReal (m + 1) + z ≤
          2 * inverseTwoPowReal (m + 1) := by linarith [hz.2.le]
      rw [two_mul_inverseTwoPowReal_succ] at hdouble
      exact hdouble.trans hinvhalf
    have hpoint : inverseTwoPowReal (m + 1) + z ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨add_nonneg (inverseTwoPowReal_pos (m + 1)).le hz.1, hsumhalf⟩
    have hfirst := hF.hasDerivAt (inverseTwoPowReal (m + 1) + z) hpoint
    have hfirstComp := hfirst.comp z
      ((hasDerivAt_const z (inverseTwoPowReal (m + 1))).add (hasDerivAt_id z))
    have hsecond := hF.hasDerivAt z hzhalf
    have hsum := hfirstComp.fun_add hsecond
    have hargEq : 2 * (inverseTwoPowReal (m + 1) + z) =
        inverseTwoPowReal m + 2 * z := by
      rw [mul_add, two_mul_inverseTwoPowReal_succ]
    have hih := ih (2 * z) (mul_nonneg (by norm_num) hz.1) hzscaled
    have hcoef :
        2 * fabiusReal F (2 * (inverseTwoPowReal (m + 1) + z)) * (0 + 1) +
            2 * fabiusReal F (2 * z) = 2 * analyticTaylorSum F m (2 * z) := by
      rw [hargEq]
      rw [← hih]
      ring
    have hsum' := hsum.congr_deriv hcoef
    have hsum'' : HasDerivAt lhs (2 * analyticTaylorSum F m (2 * z)) z := by
      simpa only [lhs, Function.comp_apply, Pi.add_apply] using hsum'
    exact hsum''.hasDerivWithinAt.mono (by intro x hx; exact hx)
  have hderivRhs : ∀ z ∈ Ico (0 : ℝ) (inverseTwoPowReal (m + 1)),
      HasDerivWithinAt rhs (2 * analyticTaylorSum F m (2 * z)) (Ici z) z := by
    intro z hz
    exact (analyticTaylorSum_derivative_identity F m z).hasDerivWithinAt.mono
      (by intro x hx; exact hx)
  have hzero : lhs 0 = rhs 0 := by
    dsimp only [lhs, rhs]
    rw [analyticTaylorSum_zero]
    simp only [analyticInverseValue]
    rw [hF.zero_of_nonpos 0 le_rfl, add_zero]
    simp
  exact eq_of_has_deriv_right_eq hderivLhs hderivRhs
    hlhsCont.continuousOn hrhsCont.continuousOn hzero y ⟨hy0, hy⟩

private theorem analytic_scale_recurrence
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) (hm : 1 ≤ m)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ inverseTwoPowReal m) :
    fabiusReal F (inverseTwoPowReal m + y) + fabiusReal F y =
      analyticTaylorSum F m y := by
  induction m generalizing y with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero => exact analytic_scale_recurrence_one F hF y hy0 hy
      | succ m =>
          exact analytic_scale_recurrence_succ F hF (m + 1) (by omega)
            (fun z hz0 hz => ih (by omega) z hz0 hz) y hy0 hy

private lemma fabiusAtInverseTwoPow_endpoint (n : ℕ) :
    fabiusAtInverseTwoPow n + fabiusAtInverseTwoPow (n + 1) =
      ∑ k ∈ range (n + 1 + 1),
        (2 : ℚ) ^ (k + 1).choose 2 * fabiusAtInverseTwoPow (n + 1 - k) *
          ((1 : ℚ) / (2 : ℚ) ^ (n + 1)) ^ k / k.factorial := by
  have hcancel := fabiusDyadic_add_remainder_eq_block (n + 1) 0 1 (by norm_num)
  have hblock := dyadicBlock_eq_taylor_sum (n + 1) 0 (by omega) (1 : ℚ)
  have hclosed :
      fabiusDyadic (n + 1) 2 + fabiusDyadic (n + 1) 1 =
        ∑ k ∈ range (n + 1 + 1),
          (2 : ℚ) ^ (k + 1).choose 2 * fabiusAtInverseTwoPow (n + 1 - k) *
            ((1 : ℚ) / (2 : ℚ) ^ (n + 1)) ^ k / k.factorial := by
    calc
      _ = _ := hcancel
      _ = _ := by
        convert hblock using 1
        · congr 1
          apply Finset.sum_congr rfl
          intro h hh
          congr 2
          norm_num
        · norm_num
  have hrefine := fabiusDyadic_refine_of_kernel dyadicKernel_has_refinement n 1
  rw [show 2 = 2 * 1 by omega, hrefine] at hclosed
  exact hclosed

private theorem analyticInverseValue_eq_fabiusAtInverseTwoPow
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    analyticInverseValue F n = (fabiusAtInverseTwoPow n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp [analyticInverseValue, inverseTwoPowReal,
          hF.one_of_one_le, fabiusAtInverseTwoPow_eq_halfMoment,
          halfMomentFabiusValue]
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        let base := inverseTwoPowReal (n + 1)
        let termA : ℕ → ℝ := fun k =>
          (2 : ℝ) ^ (k + 1).choose 2 * analyticInverseValue F (n + 1 - k) *
            base ^ k / k.factorial
        let termR : ℕ → ℝ := fun k =>
          (2 : ℝ) ^ (k + 1).choose 2 * (fabiusAtInverseTwoPow (n + 1 - k) : ℝ) *
            base ^ k / k.factorial
        have hsplitA :
            (∑ k ∈ range (n + 1 + 1), termA k) =
              termA 0 + termA 1 + ∑ j ∈ range n, termA (2 + j) := by
          rw [show n + 1 + 1 = 2 + n by omega, Finset.sum_range_add]
          simp [Finset.sum_range_succ]
        have hsplitR :
            (∑ k ∈ range (n + 1 + 1), termR k) =
              termR 0 + termR 1 + ∑ j ∈ range n, termR (2 + j) := by
          rw [show n + 1 + 1 = 2 + n by omega, Finset.sum_range_add]
          simp [Finset.sum_range_succ]
        have ha0 := analytic_scale_recurrence F hF (n + 1) (by omega)
          base (inverseTwoPowReal_pos (n + 1)).le le_rfl
        have hdouble : inverseTwoPowReal (n + 1) + base = inverseTwoPowReal n := by
          dsimp only [base]
          linarith [two_mul_inverseTwoPowReal_succ n]
        have ha :
            analyticInverseValue F n + analyticInverseValue F (n + 1) =
              ∑ k ∈ range (n + 1 + 1), termA k := by
          change fabiusReal F (inverseTwoPowReal n) +
              fabiusReal F (inverseTwoPowReal (n + 1)) = _
          rw [← hdouble]
          simpa only [analyticInverseValue, analyticTaylorSum, base, termA] using ha0
        rw [hsplitA] at ha
        norm_num [termA] at ha
        have hrQ := fabiusAtInverseTwoPow_endpoint n
        have hrCast := congrArg (fun q : ℚ => (q : ℝ)) hrQ
        push_cast at hrCast
        have hbaseReal : (1 : ℝ) / (2 : ℝ) ^ (n + 1) = base := by
          simp only [base, inverseTwoPowReal, one_div]
        rw [hbaseReal] at hrCast
        have hr :
            (fabiusAtInverseTwoPow n : ℝ) + (fabiusAtInverseTwoPow (n + 1) : ℝ) =
              ∑ k ∈ range (n + 1 + 1), termR k := by
          simpa only [termR] using hrCast
        rw [hsplitR] at hr
        norm_num [termR] at hr
        have htail :
            (∑ j ∈ range n, termA (2 + j)) =
              ∑ j ∈ range n, termR (2 + j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < n := Finset.mem_range.mp hj
          have hindex : n + 1 - (2 + j) < n := by omega
          dsimp only [termA, termR]
          rw [ih (n + 1 - (2 + j)) hindex]
        rw [htail] at ha
        have hcoeflt : 2 * base < 1 := by
          dsimp only [base]
          rw [two_mul_inverseTwoPowReal_succ]
          exact (inverseTwoPowReal_le_half n hnpos).trans_lt (by norm_num)
        have hfactor :
            (1 - 2 * base) *
                (analyticInverseValue F n - (fabiusAtInverseTwoPow n : ℝ)) = 0 := by
          linear_combination ha - hr
        exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left
          (ne_of_gt (sub_pos.mpr hcoeflt)))

private lemma analyticTaylorSum_eq_cast_horner
    (F : BoundedFabius) (hF : IsFabius F)
    (maxExponent order : ℕ) (horder : order ≤ maxExponent) (offset : ℚ) :
    analyticTaylorSum F order (offset : ℝ) =
      (fabiusTaylorHorner (fabiusInversePowTwoTable maxExponent)
        order offset : ℝ) := by
  have hq := fabiusTaylorHorner_eq_sum maxExponent order horder offset
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at hr
  rw [hr, analyticTaylorSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [analyticInverseValue_eq_fabiusAtInverseTwoPow F hF]

private theorem fabiusReal_dyadic_bit_recurrence
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha0 : 0 < a) (ha : a ≤ 2 ^ n) :
    let leadingExponent := Nat.log2 a
    let order := n - leadingExponent
    let remainder := a - 2 ^ leadingExponent
    let offset := (remainder : ℚ) / (2 : ℚ) ^ n
    fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) =
      (fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset : ℝ) -
        fabiusReal F ((remainder : ℝ) / (2 : ℝ) ^ n) := by
  dsimp only
  obtain ⟨hb, hrlt, haSplit⟩ := leading_bit_data n a ha0 ha
  let b := Nat.log2 a
  let r := a - 2 ^ b
  let order := n - b
  let offset : ℚ := (r : ℚ) / (2 : ℚ) ^ n
  change b ≤ n at hb
  change r < 2 ^ b at hrlt
  change a = 2 ^ b + r at haSplit
  change fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) =
    (fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset : ℝ) -
      fabiusReal F ((r : ℝ) / (2 : ℝ) ^ n)
  by_cases horder0 : order = 0
  · have hbn : b = n := by omega
    have haSplit' : a = 2 ^ n + r := by simpa [hbn] using haSplit
    have hrzero : r = 0 := by omega
    have haPow : a = 2 ^ n := by omega
    rw [haPow, hrzero]
    rw [hF.one_of_one_le _ (by norm_num), hF.zero_of_nonpos _ (by norm_num)]
    have hoffzero : offset = 0 := by simp [offset, hrzero]
    rw [horder0, hoffzero]
    rw [fabiusTaylorHorner, fabiusTaylorHorner.go.eq_1]
    norm_num
  · have horderPos : 1 ≤ order := Nat.one_le_iff_ne_zero.mpr horder0
    have hnadd : n = b + order := by
      dsimp only [order]
      omega
    have hbase : (2 : ℝ) ^ b / (2 : ℝ) ^ n =
        inverseTwoPowReal order := by
      rw [hnadd, pow_add]
      simp only [inverseTwoPowReal]
      field_simp
    have hoffsetCast : (offset : ℝ) = (r : ℝ) / (2 : ℝ) ^ n := by
      simp only [offset]
      push_cast
      rfl
    have hoffsetNonneg : 0 ≤ (offset : ℝ) := by
      rw [hoffsetCast]
      positivity
    have hoffsetLe : (offset : ℝ) ≤ inverseTwoPowReal order := by
      rw [hoffsetCast, ← hbase]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hrlt.le
      · positivity
    have hxSplit : (a : ℝ) / (2 : ℝ) ^ n =
        inverseTwoPowReal order + (offset : ℝ) := by
      rw [haSplit]
      push_cast
      rw [add_div, hbase, hoffsetCast]
    have hscale := analytic_scale_recurrence F hF order horderPos
      (offset : ℝ) hoffsetNonneg hoffsetLe
    rw [analyticTaylorSum_eq_cast_horner F hF n order (Nat.sub_le n b) offset]
      at hscale
    rw [eq_sub_iff_add_eq, hxSplit, ← hoffsetCast]
    exact hscale

/-- The exact closed-form evaluator takes the value `1` at the right endpoint
of every unit dyadic grid, including the scale `n = 0`. -/
theorem fabiusDyadic_unit_endpoint (n : ℕ) :
    fabiusDyadic n (2 ^ n) = 1 := by
  rw [← fabiusDyadicUnit_eq_fabiusDyadic n (2 ^ n) le_rfl,
    fabiusDyadicUnit_of_ge n (2 ^ n) le_rfl]

/-- Equation (32) evaluates the bounded Fabius function on its dyadic grid. -/
theorem fabiusDyadic_cast (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ n) :
    (fabiusDyadic n a : ℝ) = fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      by_cases ha0 : a = 0
      · subst a
        rw [fabiusDyadic_arg_zero]
        norm_num
        exact (hF.zero_of_nonpos 0 le_rfl).symm
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        let b := Nat.log2 a
        let r := a - 2 ^ b
        have hrlt : r < a := by
          dsimp only [r]
          exact Nat.sub_lt hapos (by positivity)
        have hrbound : r ≤ 2 ^ n := hrlt.le.trans ha
        have hihr := ih r hrlt hrbound
        have hrat := fabiusInversePowTwoTable_hasBitRecurrence n a hapos ha
        have hana := fabiusReal_dyadic_bit_recurrence F hF n a hapos ha
        dsimp only at hrat hana
        have hratCast := congrArg (fun q : ℚ => (q : ℝ)) hrat
        push_cast at hratCast
        rw [hratCast, hihr]
        exact hana.symm

/-- After coercion to `ℝ`, the exact rational inverse-power value agrees with
every bounded Fabius solution at `2⁻ⁿ`.  This is the `a = 1` specialization of
`fabiusDyadic_cast` and includes the endpoint `n = 0`. -/
theorem fabiusAtInverseTwoPow_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (fabiusAtInverseTwoPow n : ℝ) =
      fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  simpa only [fabiusAtInverseTwoPow, Nat.cast_one, one_div] using
    fabiusDyadic_cast F hF n 1 Nat.one_le_two_pow

/-- The executable bounded evaluator agrees with the analytic Fabius function
for every natural dyadic numerator. Numerators beyond the unit grid are
handled by the common constant value `1`. -/
theorem fabiusDyadicUnit_cast (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) :
    (fabiusDyadicUnit n a : ℝ) =
      fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n) := by
  by_cases ha : a ≤ 2 ^ n
  · rw [fabiusDyadicUnit_eq_fabiusDyadic n a ha,
      fabiusDyadic_cast F hF n a ha]
  · rw [fabiusDyadicUnit_of_ge n a (by omega)]
    norm_num
    apply (hF.one_of_one_le _ ?_).symm
    rw [le_div_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
    norm_num
    exact_mod_cast (show 2 ^ n ≤ a by omega)

end

end Fabius
