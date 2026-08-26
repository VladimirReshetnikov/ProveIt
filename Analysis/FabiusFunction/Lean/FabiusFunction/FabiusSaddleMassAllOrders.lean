import FabiusFunction.FabiusSaddleCentralAllOrders
import FabiusFunction.FabiusLambertMinorArc
import FabiusFunction.SaddleAllOrders
import FabiusFunction.FabiusSaddleCentralRadiusAsymptotics
import FabiusFunction.NegativeLaplaceScaledTailFlat
import FabiusFunction.GaussianPolynomialWholeIntegral
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# All-orders mass expansion for the Fabius saddle kernel

This module combines the arbitrary-order vertical Taylor expansion, finite
exponential substitution, Gaussian polynomial contraction, and complementary
minor-arc estimates.  Its endpoint is the full Poincaré expansion of the
normalized dyadic Lambert saddle-kernel mass.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace Fabius

open SaddleExpansion

noncomputable section

/-- For `0 < L`, the degree-`L - 1` exponential Taylor polynomial evaluated
at the epsilon-truncated dyadic Lambert exponent splits exactly into the
saddle reference polynomial plus `dyadicLambertEpsilon t ^ L` times the
finite-exponential quotient polynomial, both evaluated at `v`.  Used in this
file by `dyadicLambert_central_expTaylor_error_isBigO` and
`dyadicLambert_central_reference_error_isBigO`. -/
theorem expTaylorPolynomial_dyadicLambertExponentTruncation_eq
    (L : ℕ) (hL : 0 < L) (t v : ℝ) :
    SaddleAllOrders.expTaylorPolynomial L
        (dyadicLambertExponentTruncation (L - 1) t v) =
      (fabiusSaddleReferencePolynomial L (dyadicLambertPhase t)
          (dyadicLambertEpsilon t : ℂ)).eval (v : ℂ) +
        (dyadicLambertEpsilon t : ℂ) ^ L *
          (fabiusSaddleFiniteExpQuotientPolynomial L
            (dyadicLambertPhase t) (dyadicLambertEpsilon t : ℂ)).eval (v : ℂ) := by
  let E : ℕ → Polynomial ℂ := fun m =>
    negativeLaplaceExponentPolynomial m (dyadicLambertPhase t)
  have hfinite := eval_finiteExpSubstitutionPolynomial_eq E
    (by simp [E]) L (Polynomial.C (dyadicLambertEpsilon t : ℂ))
  have heval := congrArg (fun p : Polynomial ℂ => p.eval (v : ℂ)) hfinite
  rw [eval_finiteExpSubstitutionPolynomial] at heval
  rw [eval_expCoeffTruncPolynomial] at heval
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C] at heval
  have hrat (q : ℕ) :
      Polynomial.eval (v : ℂ)
          ((algebraMap ℚ (Polynomial ℂ)) ((q.factorial : ℚ)⁻¹)) =
        ((q.factorial : ℂ)⁻¹) := by
    rw [IsScalarTower.algebraMap_apply ℚ ℂ (Polynomial ℂ),
      Polynomial.algebraMap_apply]
    simp
  simpa only [E, SaddleAllOrders.expTaylorPolynomial,
    dyadicLambertExponentTruncation, Nat.sub_add_cancel hL,
    fabiusSaddleReferencePolynomial, fabiusSaddleFiniteExpQuotientPolynomial,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, negativeLaplaceExponentPolynomial_eval,
    map_div₀, map_natCast, Polynomial.eval_add, one_div, inv_mul_eq_div,
    hrat] using heval

/-- For each `K` there is a constant `C` with `1 ≤ C` bounding, uniformly in
`t`, both `|negativeLaplaceBoundedExponentJet n t|` and
`|negativeLaplaceJetSlope n|` for every index `n ≤ K`. -/
lemma exists_uniform_bound_negativeLaplaceExponentJets (K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ), n ≤ K → ∀ t : ℝ,
      |negativeLaplaceBoundedExponentJet n t| ≤ C ∧
        |negativeLaplaceJetSlope n| ≤ C := by
  induction K with
  | zero =>
      obtain ⟨B, hB⟩ :=
        (isBounded_range_negativeLaplaceBoundedExponentJet 0).exists_norm_le
      let C : ℝ := max 1 (max B |negativeLaplaceJetSlope 0|)
      refine ⟨C, le_max_left _ _, ?_⟩
      intro n hn t
      have hn0 : n = 0 := by omega
      subst n
      constructor
      · exact (hB _ ⟨t, rfl⟩).trans
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
  | succ K ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      obtain ⟨B, hB⟩ :=
        (isBounded_range_negativeLaplaceBoundedExponentJet (K + 1)).exists_norm_le
      let D : ℝ := max C (max B |negativeLaplaceJetSlope (K + 1)|)
      refine ⟨D, hC.trans (le_max_left _ _), ?_⟩
      intro n hn t
      by_cases hnK : n ≤ K
      · exact ⟨(hbound n hnK t).1.trans (le_max_left _ _),
          (hbound n hnK t).2.trans (le_max_left _ _)⟩
      · have hnEq : n = K + 1 := by omega
        subst n
        constructor
        · exact (hB _ ⟨t, rfl⟩).trans
            (le_trans (le_max_left _ _) (le_max_right _ _))
        · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- Given a nonnegative `C` bounding the bounded-exponent jets and the jet
slopes at all indices up to `K + 2`, the order-`m` exponent coefficient
satisfies `‖negativeLaplaceExponentCoefficient m t v‖ ≤
C * (|v| ^ m + |v| ^ (m + 2))` for every `m ≤ K`.  The factorial
denominators are discarded rather than exploited. -/
lemma norm_negativeLaplaceExponentCoefficient_le
    {K : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ (n : ℕ), n ≤ K + 2 → ∀ t : ℝ,
      |negativeLaplaceBoundedExponentJet n t| ≤ C ∧
        |negativeLaplaceJetSlope n| ≤ C)
    {m : ℕ} (hm : m ≤ K) (t v : ℝ) :
    ‖negativeLaplaceExponentCoefficient m t v‖ ≤
      C * (|v| ^ m + |v| ^ (m + 2)) := by
  cases m with
  | zero =>
      simp only [negativeLaplaceExponentCoefficient, norm_zero, pow_zero]
      exact mul_nonneg hC
        (add_nonneg zero_le_one (pow_nonneg (abs_nonneg v) _))
  | succ n =>
      have hn : n ≤ K + 2 := by omega
      have hn2 : n + 2 ≤ K + 2 := by omega
      have hjet := (hbound n hn t).1
      have hslope := (hbound (n + 2) hn2 t).2
      have hfac1 : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hfac3 : (1 : ℝ) ≤ ((n + 3).factorial : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hfirst :
          ‖Complex.I ^ (n + 1) *
              (negativeLaplaceBoundedExponentJet n t : ℂ) *
              (v : ℂ) ^ (n + 1) / ((n + 1).factorial : ℕ)‖ ≤
            C * |v| ^ (n + 1) := by
        simp only [norm_div, norm_mul, norm_pow, Complex.norm_I,
          one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_natCast]
        calc
          |negativeLaplaceBoundedExponentJet n t| * |v| ^ (n + 1) /
                ((n + 1).factorial : ℝ) ≤
              (C * |v| ^ (n + 1)) / ((n + 1).factorial : ℝ) := by
                gcongr
          _ ≤ C * |v| ^ (n + 1) :=
            div_le_self (mul_nonneg hC (pow_nonneg (abs_nonneg _) _)) hfac1
      have hsecond :
          ‖Complex.I ^ (n + 3) *
              (negativeLaplaceJetSlope (n + 2) : ℂ) *
              (v : ℂ) ^ (n + 3) / ((n + 3).factorial : ℕ)‖ ≤
            C * |v| ^ (n + 3) := by
        simp only [norm_div, norm_mul, norm_pow, Complex.norm_I,
          one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_natCast]
        calc
          |negativeLaplaceJetSlope (n + 2)| * |v| ^ (n + 3) /
                ((n + 3).factorial : ℝ) ≤
              (C * |v| ^ (n + 3)) / ((n + 3).factorial : ℝ) := by
                gcongr
          _ ≤ C * |v| ^ (n + 3) :=
            div_le_self (mul_nonneg hC (pow_nonneg (abs_nonneg _) _)) hfac3
      exact (norm_add_le _ _).trans <| by
        rw [show n + 1 + 2 = n + 3 by omega]
        calc
          _ ≤ C * |v| ^ (n + 1) + C * |v| ^ (n + 3) :=
            add_le_add hfirst hsecond
          _ = C * (|v| ^ (n + 1) + |v| ^ (n + 3)) := by ring

/-- Eventually in `t` at `atTop`, the exponent truncation through epsilon
order `M` has norm at most `1` at every `v` of the order-`N` central window
`Icc (-A) A`, where `A = fabiusSaddleCentralRadiusOrder N
(dyadicLambertPhase t)`. -/
theorem eventually_norm_dyadicLambertExponentTruncation_le_one
    (M N : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ v ∈
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      ‖dyadicLambertExponentTruncation M t v‖ ≤ 1 := by
  obtain ⟨C, hC1, hC⟩ :=
    exists_uniform_bound_negativeLaplaceExponentJets (M + 2)
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  let A : ℝ → ℝ := fun t =>
    fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)
  let eps : ℝ → ℝ := dyadicLambertEpsilon
  let B : ℝ → ℝ := fun t =>
    ∑ m ∈ Finset.range (M + 1),
      C * (eps t * A t ^ m + eps t * A t ^ (m + 2))
  have hdecay (d : ℕ) :
      Tendsto (fun t => eps t * A t ^ d) atTop (nhds 0) := by
    simpa only [eps, A, dyadicLambertEpsilon] using
      tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow_comp
        dyadicLambertPhase tendsto_dyadicLambertPhase_atTop N d
  have hB : Tendsto B atTop (nhds 0) := by
    have hsum := tendsto_finsetSum (Finset.range (M + 1)) (fun m _hm =>
      ((hdecay m).add (hdecay (m + 2))).const_mul C)
    simpa only [B, zero_add, mul_zero, Finset.sum_const_zero] using hsum
  have hBsmall : ∀ᶠ t : ℝ in atTop, B t ≤ 1 :=
    hB.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [hBsmall, tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1]
      with t hBt hphase v hv
  have hphase0 : 0 < dyadicLambertPhase t := zero_lt_one.trans_le hphase
  have hsqrt0 : 0 < Real.sqrt (dyadicLambertPhase t) := Real.sqrt_pos.2 hphase0
  have hsqrt1 : 1 ≤ Real.sqrt (dyadicLambertPhase t) := by
    nlinarith [Real.sq_sqrt hphase0.le, Real.sqrt_nonneg (dyadicLambertPhase t)]
  have heps0 : 0 ≤ eps t := by
    dsimp [eps, dyadicLambertEpsilon]
    positivity
  have heps1 : eps t ≤ 1 := by
    dsimp [eps, dyadicLambertEpsilon]
    exact inv_le_one_of_one_le₀ hsqrt1
  have hvabs : |v| ≤ A t := by
    dsimp [A]
    exact abs_le.mpr hv
  unfold dyadicLambertExponentTruncation
  calc
    ‖∑ m ∈ Finset.range (M + 1),
        (dyadicLambertEpsilon t : ℂ) ^ m *
          negativeLaplaceExponentCoefficient m (dyadicLambertPhase t) v‖ ≤
        ∑ m ∈ Finset.range (M + 1),
          ‖(dyadicLambertEpsilon t : ℂ) ^ m *
            negativeLaplaceExponentCoefficient m (dyadicLambertPhase t) v‖ :=
      norm_sum_le _ _
    _ ≤ B t := by
      apply Finset.sum_le_sum
      intro m hm
      have hmM : m ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      cases m with
      | zero =>
          simp only [negativeLaplaceExponentCoefficient, mul_zero, norm_zero,
            pow_zero, mul_one, zero_add]
          exact mul_nonneg hC0 (add_nonneg heps0
            (mul_nonneg heps0 (pow_nonneg (Real.sqrt_nonneg _) _)))
      | succ n =>
          have hpow : eps t ^ (n + 1) ≤ eps t :=
            by simpa using
              (pow_le_pow_of_le_one heps0 heps1 (by omega : 1 ≤ n + 1))
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg heps0]
          calc
            eps t ^ (n + 1) *
                ‖negativeLaplaceExponentCoefficient (n + 1)
                  (dyadicLambertPhase t) v‖ ≤
              eps t *
                (C * (|v| ^ (n + 1) + |v| ^ (n + 1 + 2))) := by
                  gcongr
                  exact norm_negativeLaplaceExponentCoefficient_le hC0
                    (fun k hk => hC k (hk.trans (by omega)) ) hmM _ _
            _ ≤ C * (eps t * A t ^ (n + 1) +
                eps t * A t ^ (n + 1 + 2)) := by
                  have hpow1 := pow_le_pow_left₀ (abs_nonneg v) hvabs (n + 1)
                  have hpow3 := pow_le_pow_left₀ (abs_nonneg v) hvabs (n + 1 + 2)
                  calc
                    eps t * (C * (|v| ^ (n + 1) + |v| ^ (n + 1 + 2))) =
                        (eps t * C) * |v| ^ (n + 1) +
                          (eps t * C) * |v| ^ (n + 1 + 2) := by ring
                    _ ≤ (eps t * C) * A t ^ (n + 1) +
                          (eps t * C) * A t ^ (n + 1 + 2) := by gcongr
                    _ = C * (eps t * A t ^ (n + 1) +
                          eps t * A t ^ (n + 1 + 2)) := by ring
            _ = C * (eps t * A t ^ (n + 1) +
                eps t * A t ^ (n + 1 + 2)) := rfl
    _ ≤ 1 := hBt

/-- Along the dyadic Lambert phase the forward scaled jet of index `n` is
`O` of `(dyadicLambertPhase t)⁻¹ ^ R` for each fixed `R`, since the jet is
`O` of `(2 ^ dyadicLambertPhase t)⁻¹`, which beats every inverse power of
the phase. -/
theorem negativeLaplaceForwardScaledJet_dyadicLambert_isBigO_inv_pow
    (n R : ℕ) :
    (fun t : ℝ => negativeLaplaceForwardScaledJet n (dyadicLambertPhase t))
      =O[atTop] (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
  have hflat := (negativeLaplaceForwardScaledJet_isBigO_inv_rpow n 1).comp_tendsto
    tendsto_dyadicLambertPhase_atTop
  have hphaseExp :
      (fun t : ℝ => (((2 : ℝ) ^ dyadicLambertPhase t)⁻¹) ^ 1)
        =o[atTop] (fun t : ℝ => (dyadicLambertPhase t) ^ (-(R : ℝ))) := by
    have hbase := isLittleO_exp_neg_mul_rpow_atTop
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (-(R : ℝ))
    have hcomp := hbase.comp_tendsto tendsto_dyadicLambertPhase_atTop
    apply hcomp.congr'
    · filter_upwards with t
      simp only [Function.comp_apply, pow_one,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [show -Real.log 2 * dyadicLambertPhase t =
          -(Real.log 2 * dyadicLambertPhase t) by ring,
        Real.exp_neg]
    · exact Filter.EventuallyEq.rfl
  apply (hflat.trans hphaseExp.isBigO).congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

/-- Filter-generic step: if a scalar family `c` is `O` of `rate`, then the
integral of `Real.exp (-(v ^ 2) / 2) * (|c i| * |v| ^ d)` over an arbitrary
set `central i` is again `O` of `rate`.  Nothing is assumed about
`central`, since the restricted measure is dominated by the whole-line one.
Used in this file by `integralOn_realGaussian_mul_finset_absPow_isBigO` and
`integral_dyadicLambertCenteredExponentDefectMajor_isBigO`. -/
lemma integralOn_realGaussian_mul_absPow_mul_isBigO
    {alpha : Type*} (l : Filter alpha) (central : alpha → Set ℝ)
    (c rate : alpha → ℝ) (d : ℕ)
    (hc : c =O[l] rate) :
    (fun i => ∫ v in central i,
      Real.exp (-(v ^ 2) / 2) * (|c i| * |v| ^ d)) =O[l] rate := by
  let g : ℝ → ℝ := fun v => Real.exp (-(v ^ 2) / 2) * |v| ^ d
  have hg : Integrable g := by
    simpa only [g] using integrable_realGaussian_mul_abs_pow d
  let I : ℝ := ∫ v : ℝ, g v
  have hI0 : 0 ≤ I := integral_nonneg fun v => by
    dsimp [g]
    positivity
  rw [isBigO_iff] at hc ⊢
  obtain ⟨C, hC⟩ := hc
  refine ⟨I * |C|, ?_⟩
  filter_upwards [hC] with i hi
  have hrestrict : (∫ v in central i, g v) ≤ I :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun v => by dsimp [g]; positivity) hg
  have hrestrict0 : 0 ≤ ∫ v in central i, g v :=
    integral_nonneg fun v => by dsimp [g]; positivity
  have hci : |c i| ≤ |C| * ‖rate i‖ := by
    calc
      |c i| = ‖c i‖ := (Real.norm_eq_abs _).symm
      _ ≤ C * ‖rate i‖ := hi
      _ ≤ |C| * ‖rate i‖ := by gcongr; exact le_abs_self C
  have hleft0 : 0 ≤ ∫ v in central i,
      Real.exp (-(v ^ 2) / 2) * (|c i| * |v| ^ d) :=
    integral_nonneg fun v => by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft0]
  have heq : (fun v : ℝ =>
      Real.exp (-(v ^ 2) / 2) * (|c i| * |v| ^ d)) =
      fun v => |c i| * g v := by
    funext v
    dsimp [g]
    ring
  rw [heq, integral_const_mul]
  calc
    |c i| * (∫ v in central i, g v) ≤
        (|C| * ‖rate i‖) * I := by gcongr
    _ = (I * |C|) * ‖rate i‖ := by ring

/-- The small parameter `dyadicLambertEpsilon` is nonnegative. -/
lemma dyadicLambertEpsilon_nonneg (t : ℝ) :
    0 ≤ dyadicLambertEpsilon t := by
  unfold dyadicLambertEpsilon
  positivity

/-- The small parameter `dyadicLambertEpsilon` is `O` of `1` at `atTop`. -/
theorem dyadicLambertEpsilon_isBigO_one :
    dyadicLambertEpsilon =O[atTop] (fun _t : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1] with t ht
  have hsqrt1 : 1 ≤ Real.sqrt (dyadicLambertPhase t) := by
    have ht0 : 0 ≤ dyadicLambertPhase t := zero_le_one.trans ht
    nlinarith [Real.sq_sqrt ht0, Real.sqrt_nonneg (dyadicLambertPhase t)]
  rw [Real.norm_eq_abs, abs_of_nonneg (dyadicLambertEpsilon_nonneg t)]
  simpa only [one_mul, norm_one] using
    (show dyadicLambertEpsilon t ≤ 1 by
      unfold dyadicLambertEpsilon
      exact inv_le_one_of_one_le₀ hsqrt1)

/-- The bounded-exponent jet of index `n`, evaluated along the dyadic
Lambert phase, is `O` of `1` at `atTop`. -/
theorem negativeLaplaceBoundedExponentJet_dyadicLambert_isBigO_one
    (n : ℕ) :
    (fun t : ℝ => negativeLaplaceBoundedExponentJet n (dyadicLambertPhase t))
      =O[atTop] (fun _t : ℝ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ :=
    (isBounded_range_negativeLaplaceBoundedExponentJet n).exists_norm_le
  apply IsBigO.of_bound C
  filter_upwards with t
  simpa using hC _ ⟨dyadicLambertPhase t, rfl⟩

/-- Each fixed inverse power `(dyadicLambertPhase t)⁻¹ ^ R` is `O` of `1` at
`atTop`. -/
theorem dyadicLambert_invPhasePow_isBigO_one (R : ℕ) :
    (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) =O[atTop]
      (fun _t : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1] with t ht
  have hinv0 : 0 ≤ (dyadicLambertPhase t)⁻¹ := by positivity
  have hinv1 : (dyadicLambertPhase t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hinv0 _), norm_one,
    mul_one]
  exact (pow_le_one₀ hinv0 hinv1)

/-- Where the phase is positive, `dyadicLambertEpsilon t ^ (2 * R)` equals
`(dyadicLambertPhase t)⁻¹ ^ R`: two powers of the small parameter are
exactly one inverse power of the phase. -/
lemma dyadicLambertEpsilon_pow_two_mul
    (R : ℕ) {t : ℝ} (ht : 0 < dyadicLambertPhase t) :
    dyadicLambertEpsilon t ^ (2 * R) =
      (dyadicLambertPhase t)⁻¹ ^ R := by
  rw [pow_mul, dyadicLambertEpsilon_sq ht]

/-- Eventually in `t` at `atTop`, `|dyadicLambertEpsilon t * v| ≤ 1 / 2` for
every `v` in the order-`N` central window.  Used in this file by
`eventually_norm_dyadicLambertCenteredExponent_sub_truncation_le_one` and
`integral_norm_dyadicLambertCenteredExponent_sub_truncation_isBigO` to
discharge the smallness hypothesis of
`norm_dyadicLambertCenteredExponent_sub_truncation_le_major`. -/
theorem eventually_dyadicLambertEpsilon_mul_abs_le_half_on_orderRadius
    (N : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ v ∈
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      |dyadicLambertEpsilon t * v| ≤ 1 / 2 := by
  have hlim := (tendsto_fabiusSaddleCentralRadiusOrder_div_sqrt N).comp
    tendsto_dyadicLambertPhase_atTop
  have hhalf : ∀ᶠ t : ℝ in atTop,
      fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t) /
          Real.sqrt (dyadicLambertPhase t) ≤ 1 / 2 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards
    [hhalf, tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0]
      with t ht hphase v hv
  have hsqrt : 0 < Real.sqrt (dyadicLambertPhase t) := Real.sqrt_pos.2 hphase
  have hvabs : |v| ≤
      fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t) := abs_le.mpr hv
  rw [abs_mul, abs_of_nonneg (dyadicLambertEpsilon_nonneg t)]
  unfold dyadicLambertEpsilon
  rw [inv_mul_eq_div]
  exact (div_le_div_of_nonneg_right hvabs hsqrt.le).trans ht

/-- The order-`m` exponent polynomial has natural degree at most `m + 2`. -/
lemma natDegree_negativeLaplaceExponentPolynomial_le
    (m : ℕ) (t : ℝ) :
    (negativeLaplaceExponentPolynomial m t).natDegree ≤ m + 2 := by
  cases m with
  | zero => simp [negativeLaplaceExponentPolynomial]
  | succ n =>
      unfold negativeLaplaceExponentPolynomial
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [max_le_iff]
      constructor
      · exact (Polynomial.natDegree_C_mul_le _ _).trans <| by
          rw [Polynomial.natDegree_X_pow]
          omega
      · exact (Polynomial.natDegree_C_mul_le _ _).trans <| by
          rw [Polynomial.natDegree_X_pow]

/-- Each fixed coefficient `d` of the order-`m` exponent polynomial,
evaluated along the dyadic Lambert phase, is `O` of `1` at `atTop`. -/
theorem negativeLaplaceExponentPolynomial_coeff_dyadicLambert_isBigO_one
    (m d : ℕ) :
    (fun t : ℝ =>
      (negativeLaplaceExponentPolynomial m (dyadicLambertPhase t)).coeff d)
      =O[atTop] (fun _t : ℝ => (1 : ℂ)) := by
  cases m with
  | zero =>
      have hz : (fun _t : ℝ => (0 : ℂ)) =O[atTop]
          (fun _t : ℝ => (1 : ℂ)) :=
        isBigO_zero (fun _t : ℝ => (1 : ℂ)) atTop
      simpa [negativeLaplaceExponentPolynomial] using
        hz
  | succ n =>
      by_cases hd1 : d = n + 1
      · subst d
        have hjet : (fun t : ℝ =>
            (negativeLaplaceBoundedExponentJet n (dyadicLambertPhase t) : ℂ))
            =O[atTop] (fun _t : ℝ => (1 : ℂ)) :=
          Complex.isBigO_ofReal_left.mpr
          (Complex.isBigO_ofReal_right.mpr
            (negativeLaplaceBoundedExponentJet_dyadicLambert_isBigO_one n))
        have hc : (fun _t : ℝ =>
            Complex.I ^ (n + 1) / ((n + 1).factorial : ℕ)) =O[atTop]
            (fun _t : ℝ => (1 : ℂ)) :=
          isBigO_const_const _ one_ne_zero atTop
        have hmain := hc.mul hjet
        by_cases heq : n + 1 = n + 3
        · omega
        · have hfun : (fun t : ℝ =>
              (negativeLaplaceExponentPolynomial (n + 1)
                (dyadicLambertPhase t)).coeff (n + 1)) =
              fun t => Complex.I ^ (n + 1) *
                (negativeLaplaceBoundedExponentJet n
                  (dyadicLambertPhase t) : ℂ) /
                    ((n + 1).factorial : ℕ) := by
            funext t
            simp only [negativeLaplaceExponentPolynomial,
              Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
              if_neg heq]
            simp
          rw [hfun]
          simpa [div_eq_mul_inv, mul_comm] using hmain
      · by_cases hd3 : d = n + 3
        · subst d
          have hc : (fun _t : ℝ =>
              Complex.I ^ (n + 3) * (negativeLaplaceJetSlope (n + 2) : ℂ) /
                ((n + 3).factorial : ℕ)) =O[atTop]
              (fun _t : ℝ => (1 : ℂ)) :=
            isBigO_const_const _ one_ne_zero atTop
          have heq : n + 3 ≠ n + 1 := by omega
          have hfun : (fun t : ℝ =>
              (negativeLaplaceExponentPolynomial (n + 1)
                (dyadicLambertPhase t)).coeff (n + 3)) =
              fun _t => Complex.I ^ (n + 3) *
                (negativeLaplaceJetSlope (n + 2) : ℂ) /
                  ((n + 3).factorial : ℕ) := by
            funext t
            simp only [negativeLaplaceExponentPolynomial,
              Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
              if_neg heq]
            simp
          rw [hfun]
          exact hc
        · have hz : (fun _t : ℝ => (0 : ℂ)) =O[atTop]
              (fun _t : ℝ => (1 : ℂ)) :=
            isBigO_zero (fun _t : ℝ => (1 : ℂ)) atTop
          simpa [negativeLaplaceExponentPolynomial,
            Polynomial.coeff_C_mul_X_pow, hd1, hd3] using hz

/-- The exponent polynomial after factoring its first small parameter. -/
noncomputable def dyadicLambertReducedExponentPolynomial
    (K : ℕ) (t : ℝ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range K,
    Polynomial.C ((dyadicLambertEpsilon t : ℂ) ^ n) *
      negativeLaplaceExponentPolynomial (n + 1) (dyadicLambertPhase t)

/-- The exponent truncation through epsilon order `K` factors as
`dyadicLambertEpsilon t` times the evaluation at `v` of the reduced exponent
polynomial; the factoring is possible because the `m = 0` term of the
truncation vanishes. -/
theorem dyadicLambertExponentTruncation_eq_epsilon_mul_reduced
    (K : ℕ) (t v : ℝ) :
    dyadicLambertExponentTruncation K t v =
      (dyadicLambertEpsilon t : ℂ) *
        (dyadicLambertReducedExponentPolynomial K t).eval (v : ℂ) := by
  unfold dyadicLambertExponentTruncation
    dyadicLambertReducedExponentPolynomial
  rw [Finset.sum_range_succ', Polynomial.eval_finsetSum]
  simp only [negativeLaplaceExponentCoefficient,
    negativeLaplaceExponentPolynomial_eval, mul_zero, add_zero,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [pow_succ']
  ring

/-- The reduced exponent polynomial of order `K` has natural degree at most
`K + 2`. -/
lemma natDegree_dyadicLambertReducedExponentPolynomial_le
    (K : ℕ) (t : ℝ) :
    (dyadicLambertReducedExponentPolynomial K t).natDegree ≤ K + 2 := by
  unfold dyadicLambertReducedExponentPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_C_mul_le _ _).trans <|
    (natDegree_negativeLaplaceExponentPolynomial_le (n + 1) _).trans (by
      have hnK := Finset.mem_range.mp hn
      omega)

/-- Each fixed coefficient `d` of the reduced exponent polynomial of order
`K` is `O` of `1` at `atTop`. -/
theorem dyadicLambertReducedExponentPolynomial_coeff_isBigO_one
    (K d : ℕ) :
    (fun t : ℝ => (dyadicLambertReducedExponentPolynomial K t).coeff d)
      =O[atTop] (fun _t : ℝ => (1 : ℂ)) := by
  unfold dyadicLambertReducedExponentPolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply IsBigO.sum
  intro n _hn
  have hepsC : (fun t : ℝ => (dyadicLambertEpsilon t : ℂ)) =O[atTop]
      (fun _t : ℝ => (1 : ℂ)) :=
    Complex.isBigO_ofReal_left.mpr
      (Complex.isBigO_ofReal_right.mpr dyadicLambertEpsilon_isBigO_one)
  have heps := hepsC.pow n
  simpa only [one_pow, one_mul] using heps.mul
    (negativeLaplaceExponentPolynomial_coeff_dyadicLambert_isBigO_one
      (n + 1) d)

/-- If every coefficient of a polynomial-valued family is `O` of `1` along a
filter, then so is every coefficient of its `q`-th power. -/
lemma polynomial_pow_coeff_isBigO_one
    {alpha : Type*} (l : Filter alpha) (p : alpha → Polynomial ℂ)
    (hp : ∀ d : ℕ, (fun i => (p i).coeff d) =O[l]
      (fun _i => (1 : ℂ)))
    (q d : ℕ) :
    (fun i => ((p i) ^ q).coeff d) =O[l] (fun _i => (1 : ℂ)) := by
  induction q generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simpa using (isBigO_refl (fun _i : alpha => (1 : ℂ)) l)
      · have hz : (fun _i : alpha => (0 : ℂ)) =O[l]
            (fun _i : alpha => (1 : ℂ)) :=
          isBigO_zero (fun _i : alpha => (1 : ℂ)) l
        simpa [Polynomial.coeff_one, hd] using hz
  | succ q ih =>
      simp only [pow_succ, Polynomial.coeff_mul]
      apply IsBigO.sum
      intro a _ha
      simpa only [one_mul] using (ih a.1).mul (hp a.2)

/-- The Gaussian factorial tail weight of the `q`-th power of the reduced
exponent polynomial of order `K` is `O` of `1` at `atTop`. -/
theorem gaussianPolynomialTailWeight_reducedExponentPow_isBigO_one
    (K q : ℕ) :
    (fun t : ℝ => gaussianPolynomialTailWeight
      ((dyadicLambertReducedExponentPolynomial K t) ^ q)) =O[atTop]
        (fun _t : ℝ => (1 : ℝ)) := by
  apply gaussianPolynomialTailWeight_isBigO_of_degree_coeff atTop
    (q * (K + 2))
  · intro t
    exact (Polynomial.natDegree_pow_le).trans
      (Nat.mul_le_mul_left q
        (natDegree_dyadicLambertReducedExponentPolynomial_le K t))
  · intro d _hd
    exact polynomial_pow_coeff_isBigO_one atTop
      (dyadicLambertReducedExponentPolynomial K)
      (dyadicLambertReducedExponentPolynomial_coeff_isBigO_one K) q d

/-- With `L = 2 * (N + 1)` and `K = L - 1`, the Gaussian-weighted `L`-th
power of the exponent truncation, integrated over the order-`N` central
window, is `O` of `(dyadicLambertPhase t)⁻¹ ^ (N + 1)`.  Used in this file
by `dyadicLambert_central_expTaylor_error_isBigO`. -/
theorem integral_dyadicLambertExponentTruncation_pow_isBigO
    (N : ℕ) :
    let L := 2 * (N + 1)
    let K := L - 1
    (fun t : ℝ => ∫ v in
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      Real.exp (-(v ^ 2) / 2) *
        ‖dyadicLambertExponentTruncation K t v‖ ^ L) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  dsimp only
  let L : ℕ := 2 * (N + 1)
  let K : ℕ := L - 1
  let p : ℝ → Polynomial ℂ := fun t =>
    (dyadicLambertReducedExponentPolynomial K t) ^ L
  let central : ℝ → Set ℝ := fun t =>
    Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
      (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
  let rate : ℝ → ℝ := fun t => (dyadicLambertPhase t)⁻¹ ^ (N + 1)
  let whole : ℝ → ℝ := fun t => ∫ v : ℝ,
    ‖QuantitativeSaddle.standardGaussian v * (p t).eval (v : ℂ)‖
  have hweight : (fun t : ℝ => gaussianPolynomialTailWeight (p t)) =O[atTop]
      (fun _t : ℝ => (1 : ℝ)) := by
    simpa only [p] using
      gaussianPolynomialTailWeight_reducedExponentPow_isBigO_one K L
  have hwhole : whole =O[atTop] (fun _t : ℝ => (1 : ℝ)) := by
    simpa only [whole] using
      integral_norm_standardGaussian_mul_eval_isBigO_of_weight atTop p hweight
  have heps : (fun t : ℝ => dyadicLambertEpsilon t ^ L) =O[atTop] rate := by
    apply (isBigO_refl rate atTop).congr'
    · filter_upwards
        [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
      dsimp [L, rate]
      exact (dyadicLambertEpsilon_pow_two_mul (N + 1) ht).symm
    · exact Filter.EventuallyEq.rfl
  have hproduct : (fun t => dyadicLambertEpsilon t ^ L * whole t) =O[atTop]
      rate := by
    simpa only [mul_one] using heps.mul hwhole
  apply (IsBigO.of_bound 1 ?_).trans hproduct
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
  have heps0 : 0 ≤ dyadicLambertEpsilon t := dyadicLambertEpsilon_nonneg t
  have hpint : Integrable (fun v : ℝ =>
      ‖QuantitativeSaddle.standardGaussian v * (p t).eval (v : ℂ)‖) :=
    (integrable_standardGaussian_mul_eval (p t)).norm
  have hpoint (v : ℝ) :
      Real.exp (-(v ^ 2) / 2) *
          ‖dyadicLambertExponentTruncation K t v‖ ^ L =
        dyadicLambertEpsilon t ^ L *
          ‖QuantitativeSaddle.standardGaussian v * (p t).eval (v : ℂ)‖ := by
    rw [dyadicLambertExponentTruncation_eq_epsilon_mul_reduced]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg heps0, mul_pow, p, Polynomial.eval_pow]
    have hG : ‖QuantitativeSaddle.standardGaussian v‖ =
        Real.exp (-(v ^ 2) / 2) := by
      unfold QuantitativeSaddle.standardGaussian
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    rw [hG, norm_pow]
    ring
  have hleft0 : 0 ≤ ∫ v in central t,
      Real.exp (-(v ^ 2) / 2) *
        ‖dyadicLambertExponentTruncation K t v‖ ^ L :=
    integral_nonneg fun v => by positivity
  have hwhole0 : 0 ≤ whole t := by
    dsimp [whole]
    exact integral_nonneg fun v => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hleft0, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg heps0 _) hwhole0)]
  simp_rw [hpoint]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun v => norm_nonneg _) hpint)
    (pow_nonneg heps0 _)

/-- The exact bounded exponent term of order `n + 1` has norm at most
`(|negativeLaplaceBoundedExponentJet n t| +
|negativeLaplaceForwardScaledJet n t|) * |v| ^ (n + 1)`, the factorial
denominator being discarded.  Used in this file by
`norm_dyadicLambertCenteredExponent_sub_truncation_le_major`. -/
lemma norm_negativeLaplaceExactExponentBoundedTerm_le
    (n : ℕ) (t v : ℝ) :
    ‖negativeLaplaceExactExponentBoundedTerm (n + 1) t v‖ ≤
      (|negativeLaplaceBoundedExponentJet n t| +
        |negativeLaplaceForwardScaledJet n t|) * |v| ^ (n + 1) := by
  unfold negativeLaplaceExactExponentBoundedTerm
  have hfac : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  calc
    |negativeLaplaceBoundedExponentJet n t -
          negativeLaplaceForwardScaledJet n t| * |v| ^ (n + 1) /
          ((n + 1).factorial : ℝ) ≤
        (|negativeLaplaceBoundedExponentJet n t| +
          |negativeLaplaceForwardScaledJet n t|) * |v| ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by
      gcongr
      exact abs_sub _ _
    _ ≤ (|negativeLaplaceBoundedExponentJet n t| +
          |negativeLaplaceForwardScaledJet n t|) * |v| ^ (n + 1) :=
      div_le_self (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (pow_nonneg (abs_nonneg _) _)) hfac

/-- A single forward-jet exponent term carrying small parameter `eps` has
norm at most `|eps| ^ (n + 1) * |negativeLaplaceForwardScaledJet n t| *
|v| ^ (n + 1)`, the factorial denominator being discarded.  Used in this
file by `norm_dyadicLambertCenteredExponent_sub_truncation_le_major`. -/
lemma norm_negativeLaplaceForwardExponentTerm_le
    (n : ℕ) (eps t v : ℝ) :
    ‖(eps : ℂ) ^ (n + 1) *
        (Complex.I ^ (n + 1) *
          (negativeLaplaceForwardScaledJet n t : ℂ) *
          (v : ℂ) ^ (n + 1) / ((n + 1).factorial : ℕ))‖ ≤
      |eps| ^ (n + 1) * |negativeLaplaceForwardScaledJet n t| *
        |v| ^ (n + 1) := by
  have hfac : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    norm_div, Complex.norm_I, one_pow, one_mul, Complex.norm_natCast]
  calc
    |eps| ^ (n + 1) *
          (|negativeLaplaceForwardScaledJet n t| * |v| ^ (n + 1) /
            ((n + 1).factorial : ℝ)) =
        (|eps| ^ (n + 1) * |negativeLaplaceForwardScaledJet n t| *
          |v| ^ (n + 1)) / ((n + 1).factorial : ℝ) := by ring
    _ ≤ |eps| ^ (n + 1) * |negativeLaplaceForwardScaledJet n t| *
          |v| ^ (n + 1) := div_le_self (by positivity) hfac

/-- Vertical Taylor remainder at order `M + 2`, for `F` satisfying
`IsFabius`.  Assuming `1 ≤ dyadicLambertPhase t`,
`|dyadicLambertEpsilon t * v| ≤ 1`, and that the `(M + 3)`-rd iterated
derivative of `negativeLaplaceVerticalLog F (2 ^ dyadicLambertPhase t)` is
bounded by `C * dyadicLambertPhase t` on `|theta| ≤ 1`, the vertical
logarithm at `dyadicLambertEpsilon t * v` differs from its order-`M + 2`
Taylor sum by at most `C * dyadicLambertPhase t *
|dyadicLambertEpsilon t * v| ^ (M + 3) / (M + 2).factorial`. -/
lemma norm_negativeLaplaceVerticalTaylorRemainder_le
    (F : BoundedFabius) (hF : IsFabius F)
    (M : ℕ) {C t v : ℝ}
    (_ht : 1 ≤ dyadicLambertPhase t)
    (htheta : |dyadicLambertEpsilon t * v| ≤ 1)
    (hderiv : ∀ {theta : ℝ}, |theta| ≤ 1 →
      ‖iteratedDeriv (M + 3)
        (negativeLaplaceVerticalLog F
          ((2 : ℝ) ^ dyadicLambertPhase t)) theta‖ ≤
          C * dyadicLambertPhase t) :
    ‖negativeLaplaceVerticalLog F
          ((2 : ℝ) ^ dyadicLambertPhase t)
          (dyadicLambertEpsilon t * v) -
        negativeLaplaceVerticalTaylorSum F (M + 2)
          (dyadicLambertPhase t) (dyadicLambertEpsilon t) v‖ ≤
      C * dyadicLambertPhase t *
          |dyadicLambertEpsilon t * v| ^ (M + 3) /
            ((M + 2).factorial : ℝ) := by
  rw [negativeLaplaceVerticalTaylorSum_eq_taylorWithinEval
    F hF (M + 2)]
  apply norm_negativeLaplaceVerticalLog_sub_taylorWithinEval_le
    F hF (Real.rpow_pos_of_pos (by norm_num) _) (M + 2)
  intro theta hthetaMem
  apply hderiv
  have htheta' : |theta - 0| ≤
      |dyadicLambertEpsilon t * v - 0| :=
    Set.abs_sub_left_of_mem_uIcc hthetaMem
  simpa only [sub_zero] using
    htheta'.trans (by simpa only [sub_zero] using htheta)

/-- For a real `theta` with `|theta| ≤ 1 / 2`, the complex logarithm
`Complex.log (1 + theta * I)` differs from `Complex.logTaylor (K + 1)` at
`theta * I` by at most `2 * |theta| ^ (K + 1)`.  Used in this file by
`norm_dyadicLambertCenteredExponent_sub_truncation_le_major`. -/
lemma norm_complexLog_sub_logTaylor_le_two_mul
    (K : ℕ) {theta : ℝ} (htheta : |theta| ≤ 1 / 2) :
    ‖Complex.log (1 + ((theta : ℂ) * Complex.I)) -
        Complex.logTaylor (K + 1) ((theta : ℂ) * Complex.I)‖ ≤
      2 * |theta| ^ (K + 1) := by
  have hnorm : ‖(theta : ℂ) * Complex.I‖ = |theta| := by simp
  have hz : ‖(theta : ℂ) * Complex.I‖ < 1 := by
    rw [hnorm]
    linarith
  have hlog := Complex.norm_log_sub_logTaylor_le K hz
  rw [hnorm] at hlog
  have hinv : (1 - |theta|)⁻¹ ≤ 2 := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - |theta| := by linarith
    calc
      (1 - |theta|)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (a := 1 - |theta|) (b := 1 / 2)
          (by linarith) (by norm_num)).2 hhalf
      _ = 2 := by norm_num
  calc
    _ ≤ |theta| ^ (K + 1) * (1 - |theta|)⁻¹ /
        ((K : ℝ) + 1) := hlog
    _ ≤ |theta| ^ (K + 1) * 2 /
        ((K : ℝ) + 1) := by
      gcongr
    _ ≤ 2 * |theta| ^ (K + 1) := by
      have hden : (1 : ℝ) ≤ (K : ℝ) + 1 := by norm_num
      calc
        _ ≤ |theta| ^ (K + 1) * 2 :=
          div_le_self
            (mul_nonneg (pow_nonneg (abs_nonneg _) _) (by norm_num)) hden
        _ = _ := by ring

/-- For all `R` and `k`, `dyadicLambertEpsilon t ^ (2 * R + k)` is `O` of
`(dyadicLambertPhase t)⁻¹ ^ R` at `atTop`. -/
theorem dyadicLambertEpsilon_pow_add_isBigO_invPhasePow
    (R k : ℕ) :
    (fun t : ℝ => dyadicLambertEpsilon t ^ (2 * R + k)) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
  have hbase : (fun t : ℝ => dyadicLambertEpsilon t ^ (2 * R))
      =O[atTop] (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
    apply (isBigO_refl
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) atTop).congr'
    · filter_upwards
        [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
      exact (dyadicLambertEpsilon_pow_two_mul R ht).symm
    · exact Filter.EventuallyEq.rfl
  have hextra := dyadicLambertEpsilon_isBigO_one.pow k
  have hmul := hbase.mul hextra
  apply hmul.congr'
  · filter_upwards with t
    rw [← pow_add]
  · filter_upwards with t
    simp

/-- `dyadicLambertPhase t * dyadicLambertEpsilon t ^ (2 * R + 2)` is `O` of
`(dyadicLambertPhase t)⁻¹ ^ R` at `atTop`: the extra phase factor is paid
for by the two spare powers of the small parameter. -/
theorem dyadicLambertPhase_mul_epsilon_pow_isBigO_invPhasePow
    (R : ℕ) :
    (fun t : ℝ => dyadicLambertPhase t *
        dyadicLambertEpsilon t ^ (2 * R + 2)) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
  apply (isBigO_refl
    (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) atTop).congr'
  · filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
    rw [show 2 * R + 2 = 2 * R + 2 by omega, pow_add,
      dyadicLambertEpsilon_sq ht,
      dyadicLambertEpsilon_pow_two_mul R ht]
    field_simp
  · exact Filter.EventuallyEq.rfl

/-- The boundary coefficient `dyadicLambertEpsilon t ^ (2 * R + k)` times
the sum of `|negativeLaplaceBoundedExponentJet n|` and
`|negativeLaplaceForwardScaledJet n|`, both taken along the phase, is `O`
of `(dyadicLambertPhase t)⁻¹ ^ R`. -/
theorem dyadicLambertBoundaryCoefficient_isBigO_invPhasePow
    (n R k : ℕ) :
    (fun t : ℝ => dyadicLambertEpsilon t ^ (2 * R + k) *
      (|negativeLaplaceBoundedExponentJet n (dyadicLambertPhase t)| +
        |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)|))
      =O[atTop] (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
  have heps := dyadicLambertEpsilon_pow_add_isBigO_invPhasePow R k
  have hrateOne := dyadicLambert_invPhasePow_isBigO_one R
  have hbound :=
    (negativeLaplaceBoundedExponentJet_dyadicLambert_isBigO_one n).abs_left
  have htail :=
    (negativeLaplaceForwardScaledJet_dyadicLambert_isBigO_inv_pow n R).abs_left
  have htailOne := htail.trans hrateOne
  have hsum := hbound.add htailOne
  have hmul := heps.mul hsum
  simpa only [mul_one] using hmul

/-- The forward coefficient `dyadicLambertEpsilon t ^ (n + 1)` times
`|negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)|` is `O` of
`(dyadicLambertPhase t)⁻¹ ^ R` for every `R`, the small parameter
contributing nothing beyond `O` of `1`. -/
theorem dyadicLambertForwardCoefficient_isBigO_invPhasePow
    (n R : ℕ) :
    (fun t : ℝ => dyadicLambertEpsilon t ^ (n + 1) *
      |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)|)
      =O[atTop] (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
  have heps := dyadicLambertEpsilon_isBigO_one.pow (n + 1)
  have htail :=
    (negativeLaplaceForwardScaledJet_dyadicLambert_isBigO_inv_pow n R).abs_left
  apply (heps.mul htail).congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards with t
    simp

/-- A positive polynomial majorant for the exact centered-exponent defect. -/
noncomputable def dyadicLambertCenteredExponentDefectMajor
    (M : ℕ) (C t v : ℝ) : ℝ :=
  (C * dyadicLambertPhase t * dyadicLambertEpsilon t ^ (M + 3) +
      2 * dyadicLambertEpsilon t ^ (M + 3)) * |v| ^ (M + 3) +
    dyadicLambertEpsilon t ^ (M + 1) *
      (|negativeLaplaceBoundedExponentJet M (dyadicLambertPhase t)| +
        |negativeLaplaceForwardScaledJet M (dyadicLambertPhase t)|) *
      |v| ^ (M + 1) +
    dyadicLambertEpsilon t ^ (M + 2) *
      (|negativeLaplaceBoundedExponentJet (M + 1) (dyadicLambertPhase t)| +
        |negativeLaplaceForwardScaledJet (M + 1) (dyadicLambertPhase t)|) *
      |v| ^ (M + 2) +
    ∑ m ∈ Finset.range (M + 1),
      match m with
      | 0 => 0
      | n + 1 =>
          dyadicLambertEpsilon t ^ (n + 1) *
            |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)| *
              |v| ^ (n + 1)

/-- Pointwise defect bound for `F` satisfying `IsFabius`: assuming
`0 ≤ C`, `1 ≤ dyadicLambertPhase t`, `|dyadicLambertEpsilon t * v| ≤ 1 / 2`,
and a `C * dyadicLambertPhase t` bound on the `(M + 3)`-rd iterated
derivative of the vertical logarithm on `|theta| ≤ 1`, the centered exponent
differs from its order-`M` truncation by at most
`dyadicLambertCenteredExponentDefectMajor M C t v`.  Used in this file by
`eventually_norm_dyadicLambertCenteredExponent_sub_truncation_le_one` and
`integral_norm_dyadicLambertCenteredExponent_sub_truncation_isBigO`. -/
theorem norm_dyadicLambertCenteredExponent_sub_truncation_le_major
    (F : BoundedFabius) (hF : IsFabius F)
    (M : ℕ) {C t v : ℝ} (hC : 0 ≤ C)
    (ht : 1 ≤ dyadicLambertPhase t)
    (htheta : |dyadicLambertEpsilon t * v| ≤ 1 / 2)
    (hderiv : ∀ {theta : ℝ}, |theta| ≤ 1 →
      ‖iteratedDeriv (M + 3)
        (negativeLaplaceVerticalLog F
          ((2 : ℝ) ^ dyadicLambertPhase t)) theta‖ ≤
          C * dyadicLambertPhase t) :
    ‖dyadicLambertCenteredExponent F t v -
        dyadicLambertExponentTruncation M t v‖ ≤
      dyadicLambertCenteredExponentDefectMajor M C t v := by
  have hphase0 : 0 < dyadicLambertPhase t := zero_lt_one.trans_le ht
  have heps0 : 0 ≤ dyadicLambertEpsilon t := dyadicLambertEpsilon_nonneg t
  have hvertical0 := norm_negativeLaplaceVerticalTaylorRemainder_le
    F hF M ht (htheta.trans (by norm_num)) hderiv
  have hfac : (1 : ℝ) ≤ ((M + 2).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hvertical :
      ‖negativeLaplaceVerticalLog F
            ((2 : ℝ) ^ dyadicLambertPhase t)
            (dyadicLambertEpsilon t * v) -
          negativeLaplaceVerticalTaylorSum F (M + 2)
            (dyadicLambertPhase t) (dyadicLambertEpsilon t) v‖ ≤
        C * dyadicLambertPhase t *
          dyadicLambertEpsilon t ^ (M + 3) * |v| ^ (M + 3) := by
    calc
      _ ≤ C * dyadicLambertPhase t *
          |dyadicLambertEpsilon t * v| ^ (M + 3) /
            ((M + 2).factorial : ℝ) := hvertical0
      _ ≤ C * dyadicLambertPhase t *
          |dyadicLambertEpsilon t * v| ^ (M + 3) := by
        apply div_le_self
        · positivity
        · exact hfac
      _ = C * dyadicLambertPhase t *
          dyadicLambertEpsilon t ^ (M + 3) * |v| ^ (M + 3) := by
        rw [abs_mul, abs_of_nonneg heps0, mul_pow]
        ring
  have hdenominator :
      ‖Complex.log (1 +
            (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I)) -
          Complex.logTaylor (M + 3)
            (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * dyadicLambertEpsilon t ^ (M + 3) * |v| ^ (M + 3) := by
    have h := norm_complexLog_sub_logTaylor_le_two_mul
      (M + 2) htheta
    rw [show M + 2 + 1 = M + 3 by omega] at h
    calc
      _ ≤ 2 * |dyadicLambertEpsilon t * v| ^ (M + 3) := h
      _ = 2 * dyadicLambertEpsilon t ^ (M + 3) * |v| ^ (M + 3) := by
        rw [abs_mul, abs_of_nonneg heps0, mul_pow]
        ring
  have hboundary0 :
      ‖(dyadicLambertEpsilon t : ℂ) ^ (M + 1) *
          negativeLaplaceExactExponentBoundedTerm (M + 1)
            (dyadicLambertPhase t) v‖ ≤
        dyadicLambertEpsilon t ^ (M + 1) *
          (|negativeLaplaceBoundedExponentJet M (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet M (dyadicLambertPhase t)|) *
          |v| ^ (M + 1) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg heps0]
    calc
      dyadicLambertEpsilon t ^ (M + 1) *
          ‖negativeLaplaceExactExponentBoundedTerm (M + 1)
            (dyadicLambertPhase t) v‖ ≤
        dyadicLambertEpsilon t ^ (M + 1) *
          ((|negativeLaplaceBoundedExponentJet M (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet M (dyadicLambertPhase t)|) *
              |v| ^ (M + 1)) :=
        mul_le_mul_of_nonneg_left
          (norm_negativeLaplaceExactExponentBoundedTerm_le M
            (dyadicLambertPhase t) v)
          (pow_nonneg heps0 _)
      _ = _ := by ring
  have hboundary1 :
      ‖(dyadicLambertEpsilon t : ℂ) ^ (M + 2) *
          negativeLaplaceExactExponentBoundedTerm (M + 2)
            (dyadicLambertPhase t) v‖ ≤
        dyadicLambertEpsilon t ^ (M + 2) *
          (|negativeLaplaceBoundedExponentJet (M + 1)
              (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet (M + 1)
              (dyadicLambertPhase t)|) * |v| ^ (M + 2) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg heps0]
    calc
      dyadicLambertEpsilon t ^ (M + 2) *
          ‖negativeLaplaceExactExponentBoundedTerm (M + 2)
            (dyadicLambertPhase t) v‖ ≤
        dyadicLambertEpsilon t ^ (M + 2) *
          ((|negativeLaplaceBoundedExponentJet (M + 1)
              (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet (M + 1)
              (dyadicLambertPhase t)|) * |v| ^ (M + 2)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg heps0 _)
        simpa [show M + 2 = (M + 1) + 1 by omega] using
          norm_negativeLaplaceExactExponentBoundedTerm_le (M + 1)
            (dyadicLambertPhase t) v
      _ = _ := by ring
  have hforward :
      ‖∑ m ∈ Finset.range (M + 1),
          (dyadicLambertEpsilon t : ℂ) ^ m *
            (match m with
            | 0 => 0
            | n + 1 =>
                Complex.I ^ (n + 1) *
                  (negativeLaplaceForwardScaledJet n
                    (dyadicLambertPhase t) : ℂ) *
                  (v : ℂ) ^ (n + 1) /
                    ((n + 1).factorial : ℕ))‖ ≤
        ∑ m ∈ Finset.range (M + 1),
          match m with
          | 0 => 0
          | n + 1 =>
              dyadicLambertEpsilon t ^ (n + 1) *
                |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)| *
                  |v| ^ (n + 1) := by
    calc
      _ ≤ ∑ m ∈ Finset.range (M + 1),
          ‖(dyadicLambertEpsilon t : ℂ) ^ m *
            (match m with
            | 0 => 0
            | n + 1 =>
                Complex.I ^ (n + 1) *
                  (negativeLaplaceForwardScaledJet n
                    (dyadicLambertPhase t) : ℂ) *
                  (v : ℂ) ^ (n + 1) /
                    ((n + 1).factorial : ℕ))‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m hm
        cases m with
        | zero => simp
        | succ n =>
            simpa only [abs_of_nonneg heps0] using
              norm_negativeLaplaceForwardExponentTerm_le n
                (dyadicLambertEpsilon t) (dyadicLambertPhase t) v
  rw [dyadicLambertCenteredExponent_sub_truncation_eq F hF M hphase0]
  unfold dyadicLambertCenteredExponentDefectMajor
  calc
    _ ≤
        ‖negativeLaplaceVerticalLog F
            ((2 : ℝ) ^ dyadicLambertPhase t)
            (dyadicLambertEpsilon t * v) -
          negativeLaplaceVerticalTaylorSum F (M + 2)
            (dyadicLambertPhase t) (dyadicLambertEpsilon t) v‖ +
        ‖Complex.log (1 +
            (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I)) -
          Complex.logTaylor (M + 3)
            (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I)‖ +
        ‖(dyadicLambertEpsilon t : ℂ) ^ (M + 1) *
          negativeLaplaceExactExponentBoundedTerm (M + 1)
            (dyadicLambertPhase t) v‖ +
        ‖(dyadicLambertEpsilon t : ℂ) ^ (M + 2) *
          negativeLaplaceExactExponentBoundedTerm (M + 2)
            (dyadicLambertPhase t) v‖ +
        ‖∑ m ∈ Finset.range (M + 1),
          (dyadicLambertEpsilon t : ℂ) ^ m *
            (match m with
            | 0 => 0
            | n + 1 =>
                Complex.I ^ (n + 1) *
                  (negativeLaplaceForwardScaledJet n
                    (dyadicLambertPhase t) : ℂ) *
                  (v : ℂ) ^ (n + 1) /
                    ((n + 1).factorial : ℕ))‖ := by
      calc
        ‖_ - _ + _ + _ - _‖ ≤ ‖_ - _ + _ + _‖ + ‖_‖ := norm_sub_le _ _
        _ ≤ (‖_ - _ + _‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖_ - _‖ + ‖_‖) + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖) + ‖_‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by
          ring_nf
          congr 2
          apply Finset.sum_congr rfl
          intro m hm
          cases m with
          | zero => simp
          | succ n => simp only; ring
    _ ≤
        (C * dyadicLambertPhase t *
            dyadicLambertEpsilon t ^ (M + 3) +
          2 * dyadicLambertEpsilon t ^ (M + 3)) * |v| ^ (M + 3) +
        dyadicLambertEpsilon t ^ (M + 1) *
          (|negativeLaplaceBoundedExponentJet M (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet M (dyadicLambertPhase t)|) *
          |v| ^ (M + 1) +
        dyadicLambertEpsilon t ^ (M + 2) *
          (|negativeLaplaceBoundedExponentJet (M + 1)
              (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet (M + 1)
              (dyadicLambertPhase t)|) * |v| ^ (M + 2) +
        ∑ m ∈ Finset.range (M + 1),
          match m with
          | 0 => 0
          | n + 1 =>
              dyadicLambertEpsilon t ^ (n + 1) *
                |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)| *
                  |v| ^ (n + 1) := by
      calc
        _ ≤
            (C * dyadicLambertPhase t *
                dyadicLambertEpsilon t ^ (M + 3) * |v| ^ (M + 3)) +
            (2 * dyadicLambertEpsilon t ^ (M + 3) * |v| ^ (M + 3)) +
            (dyadicLambertEpsilon t ^ (M + 1) *
              (|negativeLaplaceBoundedExponentJet M
                  (dyadicLambertPhase t)| +
                |negativeLaplaceForwardScaledJet M
                  (dyadicLambertPhase t)|) * |v| ^ (M + 1)) +
            (dyadicLambertEpsilon t ^ (M + 2) *
              (|negativeLaplaceBoundedExponentJet (M + 1)
                  (dyadicLambertPhase t)| +
                |negativeLaplaceForwardScaledJet (M + 1)
                  (dyadicLambertPhase t)|) * |v| ^ (M + 2)) +
            (∑ m ∈ Finset.range (M + 1),
              match m with
              | 0 => 0
              | n + 1 =>
                  dyadicLambertEpsilon t ^ (n + 1) *
                    |negativeLaplaceForwardScaledJet n
                      (dyadicLambertPhase t)| * |v| ^ (n + 1)) :=
          add_le_add
            (add_le_add
              (add_le_add
                (add_le_add hvertical hdenominator) hboundary0)
              hboundary1)
            hforward
        _ = _ := by ring

/-- Finite-sum form of `integralOn_realGaussian_mul_absPow_mul_isBigO`: the
Gaussian-weighted sum `∑ d ∈ s, |c d i| * |v| ^ d`, integrated over
`central i`, is `O` of `rate` whenever each `c d` with `d ∈ s` is. -/
lemma integralOn_realGaussian_mul_finset_absPow_isBigO
    {alpha : Type*} (l : Filter alpha) (central : alpha → Set ℝ)
    (c : ℕ → alpha → ℝ) (s : Finset ℕ) (rate : alpha → ℝ)
    (hc : ∀ d ∈ s, c d =O[l] rate) :
    (fun i => ∫ v in central i,
      Real.exp (-(v ^ 2) / 2) *
        (∑ d ∈ s, |c d i| * |v| ^ d)) =O[l] rate := by
  have hterm (d : ℕ) (hd : d ∈ s) :=
    integralOn_realGaussian_mul_absPow_mul_isBigO
      l central (c d) rate d (hc d hd)
  have hsum := IsBigO.sum (s := s) (fun d hd => hterm d hd)
  apply hsum.congr'
  · filter_upwards with i
    symm
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    intro d hd
    have hg : Integrable (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) * |v| ^ d) :=
      integrable_realGaussian_mul_abs_pow d
    have heq : (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) * (|c d i| * |v| ^ d)) =
        fun v => |c d i| *
          (Real.exp (-(v ^ 2) / 2) * |v| ^ d) := by
      funext v
      ring
    rw [heq]
    exact (hg.const_mul _).integrableOn
  · exact Filter.EventuallyEq.rfl

/-- For `0 < R` and `0 ≤ C`, the Gaussian-weighted defect majorant of order
`2 * R - 1`, integrated over the order-`N` central window, is `O` of
`(dyadicLambertPhase t)⁻¹ ^ R`.  Used in this file by
`integral_norm_dyadicLambertCenteredExponent_sub_truncation_isBigO`. -/
theorem integral_dyadicLambertCenteredExponentDefectMajor_isBigO
    (N R : ℕ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C) :
    (fun t : ℝ => ∫ v in
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      Real.exp (-(v ^ 2) / 2) *
        dyadicLambertCenteredExponentDefectMajor (2 * R - 1) C t v)
      =O[atTop] (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
  let M : ℕ := 2 * R - 1
  let central : ℝ → Set ℝ := fun t =>
    Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
      (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
  let rate : ℝ → ℝ := fun t => (dyadicLambertPhase t)⁻¹ ^ R
  let cV : ℝ → ℝ := fun t =>
    C * dyadicLambertPhase t * dyadicLambertEpsilon t ^ (2 * R + 2) +
      2 * dyadicLambertEpsilon t ^ (2 * R + 2)
  let cB0 : ℝ → ℝ := fun t =>
    dyadicLambertEpsilon t ^ (2 * R) *
      (|negativeLaplaceBoundedExponentJet M (dyadicLambertPhase t)| +
        |negativeLaplaceForwardScaledJet M (dyadicLambertPhase t)|)
  let cB1 : ℝ → ℝ := fun t =>
    dyadicLambertEpsilon t ^ (2 * R + 1) *
      (|negativeLaplaceBoundedExponentJet (2 * R)
          (dyadicLambertPhase t)| +
        |negativeLaplaceForwardScaledJet (2 * R)
          (dyadicLambertPhase t)|)
  let cF : ℕ → ℝ → ℝ := fun m t =>
    match m with
    | 0 => 0
    | n + 1 =>
        dyadicLambertEpsilon t ^ (n + 1) *
          |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)|
  have hM1 : M + 1 = 2 * R := by dsimp [M]; omega
  have hM2 : M + 2 = 2 * R + 1 := by omega
  have hM3 : M + 3 = 2 * R + 2 := by omega
  have hcV : cV =O[atTop] rate := by
    have hfirst :=
      (dyadicLambertPhase_mul_epsilon_pow_isBigO_invPhasePow R).const_mul_left C
    have hsecond :=
      (dyadicLambertEpsilon_pow_add_isBigO_invPhasePow R 2).const_mul_left 2
    apply (hfirst.add hsecond).congr'
    · filter_upwards with t
      dsimp [cV]
      ring
    · exact Filter.EventuallyEq.rfl
  have hcB0 : cB0 =O[atTop] rate := by
    apply (dyadicLambertBoundaryCoefficient_isBigO_invPhasePow M R 0).congr'
    · filter_upwards with t
      simp only [cB0, add_zero]
    · exact Filter.EventuallyEq.rfl
  have hcB1 : cB1 =O[atTop] rate := by
    simpa only [cB1, rate, add_zero] using
      dyadicLambertBoundaryCoefficient_isBigO_invPhasePow (2 * R) R 1
  have hcF : ∀ d ∈ Finset.range (2 * R), cF d =O[atTop] rate := by
    intro d hd
    cases d with
    | zero =>
        simpa only [cF] using
          (isBigO_zero rate atTop)
    | succ n =>
        simpa only [cF, rate] using
          dyadicLambertForwardCoefficient_isBigO_invPhasePow n R
  have hIV := integralOn_realGaussian_mul_absPow_mul_isBigO
    atTop central cV rate (2 * R + 2) hcV
  have hIB0 := integralOn_realGaussian_mul_absPow_mul_isBigO
    atTop central cB0 rate (2 * R) hcB0
  have hIB1 := integralOn_realGaussian_mul_absPow_mul_isBigO
    atTop central cB1 rate (2 * R + 1) hcB1
  have hIF := integralOn_realGaussian_mul_finset_absPow_isBigO
    atTop central cF (Finset.range (2 * R)) rate hcF
  have hsum := ((hIV.add hIB0).add hIB1).add hIF
  apply hsum.congr'
  · filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1] with t ht
    have hcV0 : 0 ≤ cV t := by
      dsimp [cV]
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg hC (zero_le_one.trans ht))
          (pow_nonneg (dyadicLambertEpsilon_nonneg t) _))
        (mul_nonneg (by norm_num)
          (pow_nonneg (dyadicLambertEpsilon_nonneg t) _))
    have hcB00 : 0 ≤ cB0 t := by
      dsimp [cB0]
      exact mul_nonneg (pow_nonneg (dyadicLambertEpsilon_nonneg t) _)
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcB10 : 0 ≤ cB1 t := by
      dsimp [cB1]
      exact mul_nonneg (pow_nonneg (dyadicLambertEpsilon_nonneg t) _)
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcF0 (d : ℕ) : 0 ≤ cF d t := by
      cases d with
      | zero => simp [cF]
      | succ n =>
          dsimp [cF]
          exact mul_nonneg (pow_nonneg (dyadicLambertEpsilon_nonneg t) _)
            (abs_nonneg _)
    have hgaussAbs (d : ℕ) : Integrable (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) * |v| ^ d) :=
      integrable_realGaussian_mul_abs_pow d
    have hcomp (c : ℝ) (d : ℕ) : IntegrableOn (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) * (c * |v| ^ d)) (central t) := by
      have heq : (fun v : ℝ =>
          Real.exp (-(v ^ 2) / 2) * (c * |v| ^ d)) =
          fun v => c * (Real.exp (-(v ^ 2) / 2) * |v| ^ d) := by
        funext v
        ring
      rw [heq]
      exact ((hgaussAbs d).const_mul c).integrableOn
    have hpoint : (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) *
          dyadicLambertCenteredExponentDefectMajor M C t v) =
        fun v =>
          Real.exp (-(v ^ 2) / 2) * (cV t * |v| ^ (2 * R + 2)) +
          Real.exp (-(v ^ 2) / 2) * (cB0 t * |v| ^ (2 * R)) +
          Real.exp (-(v ^ 2) / 2) * (cB1 t * |v| ^ (2 * R + 1)) +
          ∑ d ∈ Finset.range (2 * R),
            Real.exp (-(v ^ 2) / 2) * (cF d t * |v| ^ d) := by
      funext v
      unfold dyadicLambertCenteredExponentDefectMajor
      rw [hM1, hM2, hM3]
      dsimp [cV, cB0, cB1, cF]
      ring_nf
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      cases d with
      | zero => simp
      | succ n => simp; ring
    have hFint : IntegrableOn (fun v : ℝ =>
        ∑ d ∈ Finset.range (2 * R),
          Real.exp (-(v ^ 2) / 2) * (cF d t * |v| ^ d)) (central t) :=
      integrable_finsetSum _ (fun d _hd => hcomp (cF d t) d)
    change _ = ∫ v in central t,
      Real.exp (-(v ^ 2) / 2) *
        dyadicLambertCenteredExponentDefectMajor M C t v
    rw [hpoint]
    symm
    change (∫ v in central t,
      (((fun w : ℝ =>
          Real.exp (-(w ^ 2) / 2) * (cV t * |w| ^ (2 * R + 2))) +
        (fun w : ℝ =>
          Real.exp (-(w ^ 2) / 2) * (cB0 t * |w| ^ (2 * R))) +
        (fun w : ℝ =>
          Real.exp (-(w ^ 2) / 2) * (cB1 t * |w| ^ (2 * R + 1))) +
        (fun w : ℝ => ∑ d ∈ Finset.range (2 * R),
          Real.exp (-(w ^ 2) / 2) * (cF d t * |w| ^ d))) v) = _)
    simp only [Pi.add_apply]
    have hsplit0 :
        (∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cV t * |v| ^ (2 * R + 2)) +
          Real.exp (-(v ^ 2) / 2) * (cB0 t * |v| ^ (2 * R)) +
          Real.exp (-(v ^ 2) / 2) * (cB1 t * |v| ^ (2 * R + 1)) +
          ∑ d ∈ Finset.range (2 * R),
            Real.exp (-(v ^ 2) / 2) * (cF d t * |v| ^ d)) =
        (∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cV t * |v| ^ (2 * R + 2)) +
          Real.exp (-(v ^ 2) / 2) * (cB0 t * |v| ^ (2 * R)) +
          Real.exp (-(v ^ 2) / 2) * (cB1 t * |v| ^ (2 * R + 1))) +
        ∫ v in central t, ∑ d ∈ Finset.range (2 * R),
          Real.exp (-(v ^ 2) / 2) * (cF d t * |v| ^ d) := by
      simpa only [Pi.add_apply] using
        integral_add
          (((hcomp (cV t) (2 * R + 2)).add
            (hcomp (cB0 t) (2 * R))).add
              (hcomp (cB1 t) (2 * R + 1))) hFint
    have hsplit1 :
        (∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cV t * |v| ^ (2 * R + 2)) +
          Real.exp (-(v ^ 2) / 2) * (cB0 t * |v| ^ (2 * R)) +
          Real.exp (-(v ^ 2) / 2) * (cB1 t * |v| ^ (2 * R + 1))) =
        (∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cV t * |v| ^ (2 * R + 2)) +
          Real.exp (-(v ^ 2) / 2) * (cB0 t * |v| ^ (2 * R))) +
        ∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cB1 t * |v| ^ (2 * R + 1)) := by
      simpa only [Pi.add_apply] using integral_add
        ((hcomp (cV t) (2 * R + 2)).add
          (hcomp (cB0 t) (2 * R)))
        (hcomp (cB1 t) (2 * R + 1))
    have hsplit2 :
        (∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cV t * |v| ^ (2 * R + 2)) +
          Real.exp (-(v ^ 2) / 2) * (cB0 t * |v| ^ (2 * R))) =
        (∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cV t * |v| ^ (2 * R + 2))) +
        ∫ v in central t,
          Real.exp (-(v ^ 2) / 2) * (cB0 t * |v| ^ (2 * R)) := by
      simpa only [Pi.add_apply] using integral_add
        (hcomp (cV t) (2 * R + 2)) (hcomp (cB0 t) (2 * R))
    have hlast :
        (∫ v in central t, ∑ d ∈ Finset.range (2 * R),
          Real.exp (-(v ^ 2) / 2) * (cF d t * |v| ^ d)) =
        ∫ v in central t, Real.exp (-(v ^ 2) / 2) *
          (∑ d ∈ Finset.range (2 * R), cF d t * |v| ^ d) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [Finset.mul_sum]
    rw [hsplit0, hsplit1, hsplit2, hlast]
    simp only [abs_of_nonneg hcV0, abs_of_nonneg hcB00,
      abs_of_nonneg hcB10, abs_of_nonneg (hcF0 _)]
  · filter_upwards with t
    rfl

/-- For `F` satisfying `IsFabius` and `t` fixed, the centered exponent is
continuous in the Gaussian variable. -/
lemma continuous_dyadicLambertCenteredExponent
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    Continuous (dyadicLambertCenteredExponent F t) := by
  have hvertical : Continuous (fun v : ℝ =>
      negativeLaplaceVerticalLog F ((2 : ℝ) ^ dyadicLambertPhase t)
        (dyadicLambertEpsilon t * v)) := by
    have hbase : Continuous (negativeLaplaceVerticalLog F
        ((2 : ℝ) ^ dyadicLambertPhase t)) := by
      simpa only [iteratedDeriv_zero] using
        continuous_iteratedDeriv_negativeLaplaceVerticalLog F hF
          (Real.rpow_pos_of_pos (by norm_num) _) 0
    exact hbase.comp (by fun_prop)
  have harg : Continuous (fun v : ℝ =>
      (1 : ℂ) + (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hlog : Continuous (fun v : ℝ =>
      Complex.log
        (1 + (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I))) := by
    apply harg.clog
    intro v
    simp [Complex.slitPlane]
  unfold dyadicLambertCenteredExponent
  dsimp only
  fun_prop

/-- For `M` and `t` fixed, the exponent truncation is continuous in the
Gaussian variable. -/
lemma continuous_dyadicLambertExponentTruncation (M : ℕ) (t : ℝ) :
    Continuous (dyadicLambertExponentTruncation M t) := by
  unfold dyadicLambertExponentTruncation
  apply continuous_finsetSum
  intro m hm
  cases m with
  | zero => simpa [negativeLaplaceExponentCoefficient] using
      (continuous_const : Continuous (fun _v : ℝ => (0 : ℂ)))
  | succ n =>
      simp only [negativeLaplaceExponentCoefficient]
      fun_prop

/-- For `M`, `C`, and `t` fixed, the defect majorant is continuous in the
Gaussian variable. -/
lemma continuous_dyadicLambertCenteredExponentDefectMajor
    (M : ℕ) (C t : ℝ) :
    Continuous (dyadicLambertCenteredExponentDefectMajor M C t) := by
  have hsum : Continuous (fun v : ℝ =>
      ∑ m ∈ Finset.range (M + 1),
        match m with
        | 0 => 0
        | n + 1 =>
            dyadicLambertEpsilon t ^ (n + 1) *
              |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)| *
                |v| ^ (n + 1)) := by
    apply continuous_finsetSum
    intro m hm
    cases m with
    | zero => simpa using
        (continuous_const : Continuous (fun _v : ℝ => (0 : ℝ)))
    | succ n => simp only; fun_prop
  have hbase : Continuous (fun v : ℝ =>
      (C * dyadicLambertPhase t * dyadicLambertEpsilon t ^ (M + 3) +
          2 * dyadicLambertEpsilon t ^ (M + 3)) * |v| ^ (M + 3) +
        dyadicLambertEpsilon t ^ (M + 1) *
          (|negativeLaplaceBoundedExponentJet M (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet M (dyadicLambertPhase t)|) *
          |v| ^ (M + 1) +
        dyadicLambertEpsilon t ^ (M + 2) *
          (|negativeLaplaceBoundedExponentJet (M + 1)
              (dyadicLambertPhase t)| +
            |negativeLaplaceForwardScaledJet (M + 1)
              (dyadicLambertPhase t)|) * |v| ^ (M + 2)) := by
    fun_prop
  unfold dyadicLambertCenteredExponentDefectMajor
  exact hbase.add hsum

/-- For `F` satisfying `IsFabius`, the Gaussian-weighted integral over the
order-`N` central window of the defect between the centered exponent and its
truncation through epsilon order `2 * (N + 1) - 1` is `O` of
`(dyadicLambertPhase t)⁻¹ ^ (N + 1)`.  Used in this file by
`dyadicLambert_central_expTaylor_error_isBigO`. -/
theorem integral_norm_dyadicLambertCenteredExponent_sub_truncation_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun t : ℝ => ∫ v in
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      Real.exp (-(v ^ 2) / 2) *
        ‖dyadicLambertCenteredExponent F t v -
          dyadicLambertExponentTruncation (2 * (N + 1) - 1) t v‖)
      =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  let R : ℕ := N + 1
  let M : ℕ := 2 * R - 1
  let central : ℝ → Set ℝ := fun t =>
    Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
      (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
  let defect : ℝ → ℝ := fun t => ∫ v in central t,
    Real.exp (-(v ^ 2) / 2) *
      ‖dyadicLambertCenteredExponent F t v -
        dyadicLambertExponentTruncation M t v‖
  obtain ⟨C, hC, hderiv⟩ :=
    exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_rpow_le
      F hF (M + 2)
  have hmajor :
      (fun t : ℝ => ∫ v in central t,
        Real.exp (-(v ^ 2) / 2) *
          dyadicLambertCenteredExponentDefectMajor M C t v)
        =O[atTop] (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) := by
    simpa only [M] using
      integral_dyadicLambertCenteredExponentDefectMajor_isBigO
        N R (by dsimp [R]; omega) C hC
  have hdom : defect =O[atTop]
      (fun t : ℝ => ∫ v in central t,
        Real.exp (-(v ^ 2) / 2) *
          dyadicLambertCenteredExponentDefectMajor M C t v) := by
    apply IsBigO.of_bound 1
    filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1,
        eventually_dyadicLambertEpsilon_mul_abs_le_half_on_orderRadius N]
        with t ht htheta
    have hpoint (v : ℝ) (hv : v ∈ central t) :
        ‖dyadicLambertCenteredExponent F t v -
            dyadicLambertExponentTruncation M t v‖ ≤
          dyadicLambertCenteredExponentDefectMajor M C t v := by
      apply norm_dyadicLambertCenteredExponent_sub_truncation_le_major
        F hF M hC ht (htheta v (by simpa only [central] using hv))
      intro theta htheta1
      simpa only [show M + 2 + 1 = M + 3 by omega] using
        hderiv ht htheta1
    have hleftInt : IntegrableOn (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) *
          ‖dyadicLambertCenteredExponent F t v -
            dyadicLambertExponentTruncation M t v‖) (central t) := by
      apply Continuous.integrableOn_Icc
      have hd := (continuous_dyadicLambertCenteredExponent F hF t).sub
        (continuous_dyadicLambertExponentTruncation M t)
      exact (by fun_prop : Continuous (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2))).mul hd.norm
    have hmajorInt : IntegrableOn (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) *
          dyadicLambertCenteredExponentDefectMajor M C t v) (central t) := by
      apply Continuous.integrableOn_Icc
      have hm := continuous_dyadicLambertCenteredExponentDefectMajor M C t
      fun_prop
    have hleft0 : 0 ≤ defect t := by
      dsimp [defect]
      exact integral_nonneg fun v => by positivity
    have hmajor0 : 0 ≤ ∫ v in central t,
        Real.exp (-(v ^ 2) / 2) *
          dyadicLambertCenteredExponentDefectMajor M C t v := by
      apply integral_nonneg
      intro v
      have hM0 : 0 ≤ dyadicLambertCenteredExponentDefectMajor M C t v := by
        unfold dyadicLambertCenteredExponentDefectMajor
        have hphase0 : 0 ≤ dyadicLambertPhase t := zero_le_one.trans ht
        have heps0 := dyadicLambertEpsilon_nonneg t
        have hsum0 : 0 ≤ ∑ m ∈ Finset.range (M + 1),
            match m with
            | 0 => 0
            | n + 1 =>
                dyadicLambertEpsilon t ^ (n + 1) *
                  |negativeLaplaceForwardScaledJet n
                    (dyadicLambertPhase t)| * |v| ^ (n + 1) := by
          apply Finset.sum_nonneg
          intro m hm
          cases m with
          | zero => simp
          | succ n => positivity
        exact add_nonneg (add_nonneg
          (add_nonneg
            (mul_nonneg
              (add_nonneg
                (mul_nonneg (mul_nonneg hC hphase0) (pow_nonneg heps0 _))
                (mul_nonneg (by norm_num) (pow_nonneg heps0 _)))
              (pow_nonneg (abs_nonneg v) _))
            (mul_nonneg
              (mul_nonneg (pow_nonneg heps0 _)
                (add_nonneg (abs_nonneg _) (abs_nonneg _)))
              (pow_nonneg (abs_nonneg v) _)))
          (mul_nonneg
            (mul_nonneg (pow_nonneg heps0 _)
              (add_nonneg (abs_nonneg _) (abs_nonneg _)))
            (pow_nonneg (abs_nonneg v) _))) hsum0
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hleft0, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hmajor0]
    dsimp [defect]
    apply setIntegral_mono_on hleftInt hmajorInt measurableSet_Icc
    intro v hv
    exact mul_le_mul_of_nonneg_left (hpoint v hv) (Real.exp_nonneg _)
  have hresult := hdom.trans hmajor
  simpa only [defect, central, M, R] using hresult

/-- For `0 < R`, the inverse power `(dyadicLambertPhase t)⁻¹ ^ R` is `O` of
the small parameter `dyadicLambertEpsilon` at `atTop`. -/
theorem dyadicLambert_invPhasePow_isBigO_epsilon
    (R : ℕ) (hR : 0 < R) :
    (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ R) =O[atTop]
      dyadicLambertEpsilon := by
  have hepsExtra := dyadicLambertEpsilon_isBigO_one.pow (2 * R - 1)
  have hmul := (isBigO_refl dyadicLambertEpsilon atTop).mul hepsExtra
  apply hmul.congr'
  · filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
    rw [show dyadicLambertEpsilon t *
        dyadicLambertEpsilon t ^ (2 * R - 1) =
          dyadicLambertEpsilon t ^ (2 * R) by
      rw [← pow_succ']
      congr 1
      omega]
    exact dyadicLambertEpsilon_pow_two_mul R ht
  · filter_upwards with t
    simp

/-- For `F` satisfying `IsFabius`, eventually in `t` at `atTop` the centered
exponent differs from its truncation through epsilon order
`2 * (N + 1) - 1` by at most `1`, uniformly over the order-`N` central
window. -/
theorem eventually_norm_dyadicLambertCenteredExponent_sub_truncation_le_one
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ v ∈
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      ‖dyadicLambertCenteredExponent F t v -
        dyadicLambertExponentTruncation (2 * (N + 1) - 1) t v‖ ≤ 1 := by
  let R : ℕ := N + 1
  let M : ℕ := 2 * R - 1
  let A : ℝ → ℝ := fun t =>
    fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)
  let rate : ℝ → ℝ := fun t => (dyadicLambertPhase t)⁻¹ ^ R
  obtain ⟨C, hC, hderiv⟩ :=
    exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_rpow_le
      F hF (M + 2)
  let cV : ℝ → ℝ := fun t =>
    C * dyadicLambertPhase t * dyadicLambertEpsilon t ^ (2 * R + 2) +
      2 * dyadicLambertEpsilon t ^ (2 * R + 2)
  let cB0 : ℝ → ℝ := fun t =>
    dyadicLambertEpsilon t ^ (2 * R) *
      (|negativeLaplaceBoundedExponentJet M (dyadicLambertPhase t)| +
        |negativeLaplaceForwardScaledJet M (dyadicLambertPhase t)|)
  let cB1 : ℝ → ℝ := fun t =>
    dyadicLambertEpsilon t ^ (2 * R + 1) *
      (|negativeLaplaceBoundedExponentJet (2 * R)
          (dyadicLambertPhase t)| +
        |negativeLaplaceForwardScaledJet (2 * R)
          (dyadicLambertPhase t)|)
  let cF : ℕ → ℝ → ℝ := fun m t =>
    match m with
    | 0 => 0
    | n + 1 => dyadicLambertEpsilon t ^ (n + 1) *
        |negativeLaplaceForwardScaledJet n (dyadicLambertPhase t)|
  let B : ℝ → ℝ := fun t =>
    |cV t| * A t ^ (2 * R + 2) +
      |cB0 t| * A t ^ (2 * R) +
      |cB1 t| * A t ^ (2 * R + 1) +
      ∑ m ∈ Finset.range (2 * R), |cF m t| * A t ^ m
  have hrateEps : rate =O[atTop] dyadicLambertEpsilon := by
    simpa only [rate] using dyadicLambert_invPhasePow_isBigO_epsilon R
      (by dsimp [R]; omega)
  have hcoeffV : cV =O[atTop] rate := by
    have hfirst :=
      (dyadicLambertPhase_mul_epsilon_pow_isBigO_invPhasePow R).const_mul_left C
    have hsecond :=
      (dyadicLambertEpsilon_pow_add_isBigO_invPhasePow R 2).const_mul_left 2
    apply (hfirst.add hsecond).congr'
    · filter_upwards with t
      dsimp [cV]
      ring
    · exact Filter.EventuallyEq.rfl
  have hcoeffB0 : cB0 =O[atTop] rate := by
    apply (dyadicLambertBoundaryCoefficient_isBigO_invPhasePow M R 0).congr'
    · filter_upwards with t
      simp only [cB0, add_zero]
    · exact Filter.EventuallyEq.rfl
  have hcoeffB1 : cB1 =O[atTop] rate := by
    simpa only [cB1, rate, add_zero] using
      dyadicLambertBoundaryCoefficient_isBigO_invPhasePow (2 * R) R 1
  have hcoeffF : ∀ m ∈ Finset.range (2 * R), cF m =O[atTop] rate := by
    intro m hm
    cases m with
    | zero => simpa only [cF] using isBigO_zero rate atTop
    | succ n =>
        simpa only [cF, rate] using
          dyadicLambertForwardCoefficient_isBigO_invPhasePow n R
  have hterm (c : ℝ → ℝ) (d : ℕ) (hc : c =O[atTop] rate) :
      Tendsto (fun t => |c t| * A t ^ d) atTop (nhds 0) := by
    have hcEps := hc.abs_left.trans hrateEps
    have hprod := hcEps.mul (isBigO_refl (fun t => A t ^ d) atTop)
    exact hprod.trans_tendsto <| by
      simpa only [A, dyadicLambertEpsilon] using
        tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow_comp
          dyadicLambertPhase tendsto_dyadicLambertPhase_atTop N d
  have hB : Tendsto B atTop (nhds 0) := by
    have hsum := tendsto_finsetSum (Finset.range (2 * R))
      (fun m hm => hterm (cF m) m (hcoeffF m hm))
    simpa only [B, zero_add, Finset.sum_const_zero, add_zero] using
      (((hterm cV (2 * R + 2) hcoeffV).add
        (hterm cB0 (2 * R) hcoeffB0)).add
          (hterm cB1 (2 * R + 1) hcoeffB1)).add hsum
  have hBsmall : ∀ᶠ t : ℝ in atTop, B t ≤ 1 :=
    hB.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hBsmall,
      tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1,
      eventually_dyadicLambertEpsilon_mul_abs_le_half_on_orderRadius N]
    with t hBt ht htheta v hv
  have hmajor := norm_dyadicLambertCenteredExponent_sub_truncation_le_major
    F hF M hC ht (htheta v hv) (by
      intro theta htheta1
      simpa only [show M + 2 + 1 = M + 3 by omega] using
        hderiv ht htheta1)
  have hvabs : |v| ≤ A t := by
    dsimp [A]
    exact abs_le.mpr hv
  have hA0 : 0 ≤ A t := by
    dsimp [A]
    exact Real.sqrt_nonneg _
  have hcV0 : 0 ≤ cV t := by
    dsimp [cV]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hC (zero_le_one.trans ht))
        (pow_nonneg (dyadicLambertEpsilon_nonneg t) _))
      (mul_nonneg (by norm_num)
        (pow_nonneg (dyadicLambertEpsilon_nonneg t) _))
  have hcB00 : 0 ≤ cB0 t := by
    dsimp [cB0]
    exact mul_nonneg
      (pow_nonneg (dyadicLambertEpsilon_nonneg t) _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hcB10 : 0 ≤ cB1 t := by
    dsimp [cB1]
    exact mul_nonneg
      (pow_nonneg (dyadicLambertEpsilon_nonneg t) _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hcF0 (m : ℕ) : 0 ≤ cF m t := by
    cases m with
    | zero => simp [cF]
    | succ n =>
        dsimp [cF]
        exact mul_nonneg (pow_nonneg (dyadicLambertEpsilon_nonneg t) _)
          (abs_nonneg _)
  have hcomponent (c : ℝ) (d : ℕ) (hc0 : 0 ≤ c) :
      c * |v| ^ d ≤ |c| * A t ^ d := by
    calc
      c * |v| ^ d ≤ c * A t ^ d := by
        apply mul_le_mul_of_nonneg_left _ hc0
        exact pow_le_pow_left₀ (abs_nonneg v) hvabs d
      _ ≤ |c| * A t ^ d :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (pow_nonneg hA0 _)
  have hM1 : M + 1 = 2 * R := by dsimp [M]; omega
  have hM2 : M + 2 = 2 * R + 1 := by omega
  have hM3 : M + 3 = 2 * R + 2 := by omega
  calc
    _ ≤ dyadicLambertCenteredExponentDefectMajor M C t v := hmajor
    _ ≤ B t := by
      unfold dyadicLambertCenteredExponentDefectMajor
      rw [hM1, hM2, hM3]
      dsimp [B, cV, cB0, cB1, cF]
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact hcomponent (cV t) (2 * R + 2) hcV0
          · exact hcomponent (cB0 t) (2 * R) hcB00
        · exact hcomponent (cB1 t) (2 * R + 1) hcB10
      · apply Finset.sum_le_sum
        intro m hm
        cases m with
        | zero => simp
        | succ n =>
            simpa only [cF] using
              hcomponent (cF (n + 1) t) (n + 1) (hcF0 (n + 1))
    _ ≤ 1 := hBt

/-- For `F` satisfying `IsFabius`, with `L = 2 * (N + 1)` and `M = L - 1`,
the integral over the order-`N` central window of the norm difference
between the dyadic Lambert kernel and the Gaussian exponential-Taylor
reference built from the order-`M` exponent truncation is `O` of
`(dyadicLambertPhase t)⁻¹ ^ (N + 1)`. -/
theorem dyadicLambert_central_expTaylor_error_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    let L := 2 * (N + 1)
    let M := L - 1
    (fun t : ℝ => ∫ v in
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      ‖SaddleLambert.dyadicLambertKernel F t v -
        SaddleAllOrders.gaussianExpTaylorReference L
          (dyadicLambertExponentTruncation M t) v‖) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  dsimp only
  let L : ℕ := 2 * (N + 1)
  let M : ℕ := L - 1
  let central : ℝ → Set ℝ := fun t =>
    Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
      (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
  let E : ℝ → ℝ → ℂ := dyadicLambertCenteredExponent F
  let P : ℝ → ℝ → ℂ := fun t => dyadicLambertExponentTruncation M t
  let K : ℝ → ℝ → ℂ := SaddleLambert.dyadicLambertKernel F
  let major : ℝ → ℝ → ℝ := fun t v =>
    Real.exp 1 *
      (2 * (Real.exp (-(v ^ 2) / 2) * ‖E t v - P t v‖) +
        Real.exp (-(v ^ 2) / 2) * ‖P t v‖ ^ L)
  have hK : ∀ᶠ t : ℝ in atTop, Integrable (K t) := by
    filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
    exact integrable_fabius_scaledSaddleKernel F hF
      ((2 : ℝ) ^ (-t)) (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
      (dyadicLambertPhase t) (fabiusLambertRadius_pos _) ht
  have href : ∀ᶠ t : ℝ in atTop,
      Integrable (SaddleAllOrders.gaussianExpTaylorReference L (P t)) := by
    filter_upwards with t
    let p : Polynomial ℂ :=
      fabiusSaddleReferencePolynomial L (dyadicLambertPhase t)
          (dyadicLambertEpsilon t : ℂ) +
        Polynomial.C ((dyadicLambertEpsilon t : ℂ) ^ L) *
          fabiusSaddleFiniteExpQuotientPolynomial L
            (dyadicLambertPhase t) (dyadicLambertEpsilon t : ℂ)
    have hp := integrable_standardGaussian_mul_eval p
    apply hp.congr
    filter_upwards with v
    unfold SaddleAllOrders.gaussianExpTaylorReference
    dsimp [P]
    rw [expTaylorPolynomial_dyadicLambertExponentTruncation_eq
      L (by dsimp [L]; omega)]
    dsimp [p]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have hmajorInt : ∀ᶠ t : ℝ in atTop,
      IntegrableOn (major t) (central t) := by
    filter_upwards with t
    have hdef : Continuous (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) * ‖E t v - P t v‖) := by
      have hd := (continuous_dyadicLambertCenteredExponent F hF t).sub
        (continuous_dyadicLambertExponentTruncation M t)
      exact (by fun_prop : Continuous (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2))).mul hd.norm
    have hpow : Continuous (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) * ‖P t v‖ ^ L) := by
      have hp := continuous_dyadicLambertExponentTruncation M t
      fun_prop
    exact (hdef.const_mul 2 |>.add hpow |>.const_mul (Real.exp 1)).integrableOn_Icc
  have hmajorNonneg : ∀ᶠ t : ℝ in atTop, ∀ v ∈ central t, 0 ≤ major t v := by
    filter_upwards with t v hv
    dsimp [major]
    positivity
  have hrepr : ∀ᶠ t : ℝ in atTop, ∀ v ∈ central t,
      K t v = QuantitativeSaddle.standardGaussian v * Complex.exp (E t v) := by
    filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0,
        eventually_dyadicLambertPhase_domain] with t ht hsmall v hv
    exact dyadicLambertKernel_eq_gaussian_exp_centered F hF ht hsmall
  have hPsmall : ∀ᶠ t : ℝ in atTop, ∀ v ∈ central t, ‖P t v‖ ≤ 1 := by
    simpa only [P, central, M, L] using
      eventually_norm_dyadicLambertExponentTruncation_le_one
        (2 * (N + 1) - 1) N
  have hsmall : ∀ᶠ t : ℝ in atTop, ∀ v ∈ central t,
      ‖E t v - P t v‖ ≤ 1 := by
    simpa only [E, P, central, M, L] using
      eventually_norm_dyadicLambertCenteredExponent_sub_truncation_le_one
        F hF N
  have hmajorBound : ∀ᶠ t : ℝ in atTop, ∀ v ∈ central t,
      Real.exp (-(v ^ 2) / 2) * Real.exp ‖P t v‖ *
          (2 * ‖E t v - P t v‖ + ‖P t v‖ ^ L) ≤ major t v := by
    filter_upwards [hPsmall] with t hPt v hv
    have hexp : Real.exp ‖P t v‖ ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (hPt v hv)
    dsimp [major]
    calc
      _ ≤ Real.exp (-(v ^ 2) / 2) * Real.exp 1 *
          (2 * ‖E t v - P t v‖ + ‖P t v‖ ^ L) := by
        gcongr
      _ = _ := by ring
  have hdefInt :=
    integral_norm_dyadicLambertCenteredExponent_sub_truncation_isBigO
      F hF N
  have hpowInt := integral_dyadicLambertExponentTruncation_pow_isBigO N
  have hmajor : (fun t => ∫ v in central t, major t v) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
    have hsum :=
      ((hdefInt.const_mul_left 2).add hpowInt).const_mul_left (Real.exp 1)
    apply hsum.congr'
    · filter_upwards with t
      have hdefCont : Continuous (fun v : ℝ =>
          Real.exp (-(v ^ 2) / 2) * ‖E t v - P t v‖) := by
        have hd := (continuous_dyadicLambertCenteredExponent F hF t).sub
          (continuous_dyadicLambertExponentTruncation M t)
        exact (by fun_prop : Continuous (fun v : ℝ =>
          Real.exp (-(v ^ 2) / 2))).mul hd.norm
      have hpowCont : Continuous (fun v : ℝ =>
          Real.exp (-(v ^ 2) / 2) * ‖P t v‖ ^ L) := by
        have hp := continuous_dyadicLambertExponentTruncation M t
        fun_prop
      have hdefOn : IntegrableOn (fun v : ℝ =>
          2 * (Real.exp (-(v ^ 2) / 2) * ‖E t v - P t v‖)) (central t) := by
        dsimp [central]
        exact (hdefCont.const_mul 2).integrableOn_Icc
      have hpowOn : IntegrableOn (fun v : ℝ =>
          Real.exp (-(v ^ 2) / 2) * ‖P t v‖ ^ L) (central t) := by
        dsimp [central]
        exact hpowCont.integrableOn_Icc
      have hsplit := integral_add hdefOn hpowOn
      dsimp [major]
      rw [integral_const_mul, hsplit]
      simp only [integral_const_mul]
      dsimp [E, P, central, M, L]
    · exact Filter.EventuallyEq.rfl
  apply SaddleAllOrders.central_expTaylor_error_isBigO atTop L
    (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1))
    K E P central major hK href
    (Filter.Eventually.of_forall fun t => measurableSet_Icc)
    hmajorInt hmajorNonneg hrepr hsmall hmajorBound hmajor

/-- For `F` satisfying `IsFabius`, the integral over the order-`N` central
window of the norm difference between the dyadic Lambert kernel and the
Gaussian-weighted `dyadicLambertReferencePolynomial N` is `O` of
`(dyadicLambertPhase t)⁻¹ ^ (N + 1)`.  This is the central half of the
input to `fabiusSaddleKernelMass_dyadicLambert_sub_partialSum_isBigO`. -/
theorem dyadicLambert_central_reference_error_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun t : ℝ => ∫ v in
      Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)),
      ‖SaddleLambert.dyadicLambertKernel F t v -
        QuantitativeSaddle.standardGaussian v *
          (dyadicLambertReferencePolynomial N t).eval (v : ℂ)‖)
      =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  let L : ℕ := 2 * (N + 1)
  let M : ℕ := L - 1
  let central : ℝ → Set ℝ := fun t =>
    Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
      (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
  let K : ℝ → ℝ → ℂ := SaddleLambert.dyadicLambertKernel F
  let T : ℝ → ℝ → ℂ := fun t =>
    SaddleAllOrders.gaussianExpTaylorReference L
      (dyadicLambertExponentTruncation M t)
  let Q : ℝ → Polynomial ℂ := fun t =>
    fabiusSaddleFiniteExpQuotientPolynomial L
      (dyadicLambertPhase t) (dyadicLambertEpsilon t : ℂ)
  let Ref : ℝ → ℝ → ℂ := fun t v =>
    QuantitativeSaddle.standardGaussian v *
      (dyadicLambertReferencePolynomial N t).eval (v : ℂ)
  have hcentralTaylor :
      (fun t => ∫ v in central t, ‖K t v - T t v‖) =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
    simpa only [central, K, T, L, M] using
      dyadicLambert_central_expTaylor_error_isBigO F hF N
  have heps1 : ∀ᶠ t : ℝ in atTop, ‖(dyadicLambertEpsilon t : ℂ)‖ ≤ 1 := by
    filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1] with t ht
    have hsqrt1 : 1 ≤ Real.sqrt (dyadicLambertPhase t) := by
      have ht0 : 0 ≤ dyadicLambertPhase t := zero_le_one.trans ht
      nlinarith [Real.sq_sqrt ht0, Real.sqrt_nonneg (dyadicLambertPhase t)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (dyadicLambertEpsilon_nonneg t)]
    unfold dyadicLambertEpsilon
    exact inv_le_one_of_one_le₀ hsqrt1
  have hQweight :=
    gaussianPolynomialTailWeight_fabiusSaddleFiniteExpQuotientPolynomial_isBigO
      atTop L dyadicLambertPhase
        (fun t : ℝ => (dyadicLambertEpsilon t : ℂ)) heps1
  have hQwhole :=
    integral_norm_standardGaussian_mul_eval_isBigO_of_weight atTop Q (by
      simpa only [Q] using hQweight)
  have hepsL : (fun t : ℝ => dyadicLambertEpsilon t ^ L) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
    simpa only [L, add_zero] using
      dyadicLambertEpsilon_pow_add_isBigO_invPhasePow (N + 1) 0
  have hproduct : (fun t : ℝ => dyadicLambertEpsilon t ^ L *
      ∫ v : ℝ, ‖QuantitativeSaddle.standardGaussian v *
        (Q t).eval (v : ℂ)‖) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
    simpa only [mul_one] using hepsL.mul hQwhole
  have hquotient :
      (fun t => ∫ v in central t, ‖T t v - Ref t v‖) =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
    apply (IsBigO.of_bound 1 ?_).trans hproduct
    filter_upwards with t
    have heps0 := dyadicLambertEpsilon_nonneg t
    have hQint := (integrable_standardGaussian_mul_eval (Q t)).norm
    have hpoint (v : ℝ) :
        ‖T t v - Ref t v‖ = dyadicLambertEpsilon t ^ L *
          ‖QuantitativeSaddle.standardGaussian v * (Q t).eval (v : ℂ)‖ := by
      dsimp [T, Ref]
      unfold SaddleAllOrders.gaussianExpTaylorReference
      rw [expTaylorPolynomial_dyadicLambertExponentTruncation_eq
        L (by dsimp [L]; omega)]
      rw [show dyadicLambertReferencePolynomial N t =
          fabiusSaddleReferencePolynomial L (dyadicLambertPhase t)
            (dyadicLambertEpsilon t : ℂ) by
        unfold dyadicLambertReferencePolynomial
        congr 2]
      dsimp [Q]
      rw [mul_add, add_sub_cancel_left, ← mul_assoc]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg heps0]
      ring
    have hleftInt : IntegrableOn (fun v => ‖T t v - Ref t v‖) (central t) := by
      apply hQint.const_mul (dyadicLambertEpsilon t ^ L) |>.integrableOn.congr
      filter_upwards with v
      rw [hpoint]
    have hleft0 : 0 ≤ ∫ v in central t, ‖T t v - Ref t v‖ :=
      integral_nonneg fun v => norm_nonneg _
    have hright0 : 0 ≤ dyadicLambertEpsilon t ^ L *
        ∫ v : ℝ, ‖QuantitativeSaddle.standardGaussian v *
          (Q t).eval (v : ℂ)‖ :=
      mul_nonneg (pow_nonneg heps0 _) (integral_nonneg fun v => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hleft0, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hright0]
    simp_rw [hpoint]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun v => norm_nonneg _) hQint)
      (pow_nonneg heps0 _)
  have hsum := hcentralTaylor.add hquotient
  apply (IsBigO.of_bound 1 ?_).trans hsum
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
  have hKint : Integrable (K t) := integrable_fabius_scaledSaddleKernel F hF
    ((2 : ℝ) ^ (-t)) (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    (dyadicLambertPhase t) (fabiusLambertRadius_pos _) ht
  have hTint : Integrable (T t) := by
    let p : Polynomial ℂ :=
      fabiusSaddleReferencePolynomial L (dyadicLambertPhase t)
          (dyadicLambertEpsilon t : ℂ) +
        Polynomial.C ((dyadicLambertEpsilon t : ℂ) ^ L) * Q t
    have hp := integrable_standardGaussian_mul_eval p
    apply hp.congr
    filter_upwards with v
    dsimp [T]
    unfold SaddleAllOrders.gaussianExpTaylorReference
    rw [expTaylorPolynomial_dyadicLambertExponentTruncation_eq
      L (by dsimp [L]; omega)]
    dsimp [p]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Q]
  have hRefint : Integrable (Ref t) := by
    dsimp [Ref]
    exact integrable_standardGaussian_mul_eval _
  have hleftInt : IntegrableOn (fun v => ‖K t v - Ref t v‖) (central t) :=
    (hKint.sub hRefint).norm.integrableOn
  have hrightInt : IntegrableOn (fun v =>
      ‖K t v - T t v‖ + ‖T t v - Ref t v‖) (central t) :=
    ((hKint.sub hTint).norm.add (hTint.sub hRefint).norm).integrableOn
  have hleft0 : 0 ≤ ∫ v in central t, ‖K t v - Ref t v‖ :=
    integral_nonneg fun v => norm_nonneg _
  have hright0 : 0 ≤
      (∫ v in central t, ‖K t v - T t v‖) +
        ∫ v in central t, ‖T t v - Ref t v‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft0, one_mul,
    Real.norm_eq_abs, abs_of_nonneg hright0]
  have hsplit :
      (∫ v in central t, ‖K t v - T t v‖ + ‖T t v - Ref t v‖) =
        (∫ v in central t, ‖K t v - T t v‖) +
          ∫ v in central t, ‖T t v - Ref t v‖ := by
    simpa only [Pi.add_apply, Pi.sub_apply] using integral_add
      (hKint.sub hTint).norm.integrableOn
      (hTint.sub hRefint).norm.integrableOn
  rw [← hsplit]
  apply setIntegral_mono_on hleftInt hrightInt measurableSet_Icc
  intro v hv
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- For `F` satisfying `IsFabius`, the integral of the norm of the dyadic
Lambert kernel over the complement of the order-`N` central window is `O` of
`(dyadicLambertPhase t)⁻¹ ^ (N + 1)`. -/
theorem integral_norm_dyadicLambertKernel_orderRadius_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun t : ℝ => ∫ v in
      (Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)))ᶜ,
      ‖SaddleLambert.dyadicLambertKernel F t v‖) =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  simpa only [SaddleLambert.dyadicLambertKernel] using
    integral_norm_fabius_scaledSaddleKernel_orderRadius_isBigO
      atTop N F hF
      (fun t : ℝ => (2 : ℝ) ^ (-t))
      (fun t : ℝ => fabiusLambertRadius ((2 : ℝ) ^ (-t)))
      dyadicLambertPhase dyadicLambertExtractionCount
      (Filter.Eventually.of_forall fun t => fabiusLambertRadius_pos _)
      tendsto_dyadicLambertPhase_atTop
      (Filter.Eventually.of_forall
        dyadicLambertPhase_div_four_le_extractionCount)
      negativeLaplaceMinorArcConstant_dyadicLambert_isBigO

/-- The integral of the norm of the Gaussian-weighted
`dyadicLambertReferencePolynomial N` over the complement of the order-`N`
central window is `O` of `(dyadicLambertPhase t)⁻¹ ^ (N + 1)`.  No Fabius
hypothesis appears: the reference is an explicit polynomial. -/
theorem integral_norm_dyadicLambertReference_orderRadius_isBigO
    (N : ℕ) :
    (fun t : ℝ => ∫ v in
      (Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)))ᶜ,
      ‖QuantitativeSaddle.standardGaussian v *
        (dyadicLambertReferencePolynomial N t).eval (v : ℂ)‖) =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  have heps1 : ∀ᶠ t : ℝ in atTop, ‖(dyadicLambertEpsilon t : ℂ)‖ ≤ 1 := by
    filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1] with t ht
    have hsqrt1 : 1 ≤ Real.sqrt (dyadicLambertPhase t) := by
      have ht0 : 0 ≤ dyadicLambertPhase t := zero_le_one.trans ht
      nlinarith [Real.sq_sqrt ht0, Real.sqrt_nonneg (dyadicLambertPhase t)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (dyadicLambertEpsilon_nonneg t)]
    unfold dyadicLambertEpsilon
    exact inv_le_one_of_one_le₀ hsqrt1
  have hweight :=
    gaussianPolynomialTailWeight_fabiusSaddleReferencePolynomial_isBigO
      atTop (2 * (N + 1)) dyadicLambertPhase
        (fun t : ℝ => (dyadicLambertEpsilon t : ℂ)) heps1
  simpa only [dyadicLambertReferencePolynomial] using
    integral_norm_standardGaussian_mul_eval_orderRadius_isBigO
      atTop N dyadicLambertPhase
      (fun t : ℝ => fabiusSaddleReferencePolynomial (2 * (N + 1))
        (dyadicLambertPhase t) (dyadicLambertEpsilon t : ℂ))
      tendsto_dyadicLambertPhase_atTop hweight

/-- For `F` satisfying `IsFabius`, the integral over the complement of the
order-`N` central window of the norm difference between the dyadic Lambert
kernel and the Gaussian-weighted `dyadicLambertReferencePolynomial N` is `O`
of `(dyadicLambertPhase t)⁻¹ ^ (N + 1)`.  This is the tail half of the input
to `fabiusSaddleKernelMass_dyadicLambert_sub_partialSum_isBigO`. -/
theorem dyadicLambert_reference_tail_error_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun t : ℝ => ∫ v in
      (Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
        (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t)))ᶜ,
      ‖SaddleLambert.dyadicLambertKernel F t v -
        QuantitativeSaddle.standardGaussian v *
          (dyadicLambertReferencePolynomial N t).eval (v : ℂ)‖)
      =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  have hsum := (integral_norm_dyadicLambertKernel_orderRadius_isBigO F hF N).add
    (integral_norm_dyadicLambertReference_orderRadius_isBigO N)
  apply (IsBigO.of_bound 1 ?_).trans hsum
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
  let central := Icc
    (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
    (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
  let K := SaddleLambert.dyadicLambertKernel F t
  let Ref : ℝ → ℂ := fun v => QuantitativeSaddle.standardGaussian v *
    (dyadicLambertReferencePolynomial N t).eval (v : ℂ)
  have hKint : Integrable K := integrable_fabius_scaledSaddleKernel F hF
    ((2 : ℝ) ^ (-t)) (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    (dyadicLambertPhase t) (fabiusLambertRadius_pos _) ht
  have hRefint : Integrable Ref := by
    dsimp [Ref]
    exact integrable_standardGaussian_mul_eval _
  have hleft0 : 0 ≤ ∫ v in centralᶜ, ‖K v - Ref v‖ :=
    integral_nonneg fun v => norm_nonneg _
  have hright0 : 0 ≤
      (∫ v in centralᶜ, ‖K v‖) + ∫ v in centralᶜ, ‖Ref v‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft0, one_mul,
    Real.norm_eq_abs, abs_of_nonneg hright0]
  have hsplit :
      (∫ v in centralᶜ, ‖K v‖ + ‖Ref v‖) =
        (∫ v in centralᶜ, ‖K v‖) + ∫ v in centralᶜ, ‖Ref v‖ := by
    simpa only [Pi.add_apply] using integral_add hKint.norm.integrableOn
      hRefint.norm.integrableOn
  rw [← hsplit]
  apply setIntegral_mono_on (hKint.sub hRefint).norm.integrableOn
    (hKint.norm.add hRefint.norm).integrableOn measurableSet_Icc.compl
  intro v hv
  exact norm_sub_le _ _

/-- The normalized dyadic Lambert kernel mass through order `N`, with the
first omitted inverse-phase power as an explicit Big-O remainder. -/
theorem fabiusSaddleKernelMass_dyadicLambert_sub_partialSum_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun t : ℝ =>
      fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (fabiusLambertPhase ((2 : ℝ) ^ (-t))) -
        ∑ j ∈ Finset.range (N + 1),
          (dyadicLambertPhase t)⁻¹ ^ j *
            (fabiusSaddleMassCoefficient j (dyadicLambertPhase t) : ℂ))
      =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1)) := by
  let K : ℝ → ℝ → ℂ := SaddleLambert.dyadicLambertKernel F
  let Ref : ℝ → ℝ → ℂ := fun t v =>
    QuantitativeSaddle.standardGaussian v *
      (dyadicLambertReferencePolynomial N t).eval (v : ℂ)
  let central : ℝ → Set ℝ := fun t =>
    Icc (-fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
      (fabiusSaddleCentralRadiusOrder N (dyadicLambertPhase t))
  have hK : ∀ᶠ t : ℝ in atTop, Integrable (K t) := by
    filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
    exact integrable_fabius_scaledSaddleKernel F hF
      ((2 : ℝ) ^ (-t)) (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
      (dyadicLambertPhase t) (fabiusLambertRadius_pos _) ht
  have hRef : ∀ᶠ t : ℝ in atTop, Integrable (Ref t) := by
    filter_upwards with t
    dsimp [Ref]
    exact integrable_standardGaussian_mul_eval _
  have hnormalized :=
    SaddleAllOrders.normalizedIntegral_sub_reference_isBigO_of_central_tail
      atTop (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (N + 1))
      K Ref central hK hRef
      (Filter.Eventually.of_forall fun _t => measurableSet_Icc)
      (by simpa only [K, Ref, central] using
        dyadicLambert_central_reference_error_isBigO F hF N)
      (by simpa only [K, Ref, central] using
        dyadicLambert_reference_tail_error_isBigO F hF N)
  apply hnormalized.congr'
  · filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t ht
    rw [← gaussianPolynomialContraction_eq_integral,
      gaussianPolynomialContraction_dyadicLambertReferencePolynomial N ht]
    simp only [K, fabiusSaddleKernelMass,
      SaddleLambert.dyadicLambertKernel, fabiusLambertPhase_dyadic]
  · exact Filter.EventuallyEq.rfl

/-- The normalized dyadic Lambert saddle kernel admits its full Poincaré
expansion, with the periodic Gaussian contractions as coefficients. -/
theorem fabiusSaddleKernelMass_dyadicLambert_hasAsymptoticExpansion
    (F : BoundedFabius) (hF : IsFabius F) :
    HasAsymptoticExpansion atTop
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      (fun t : ℝ =>
        fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (fabiusLambertPhase ((2 : ℝ) ^ (-t))))
      (fun j t =>
        (fabiusSaddleMassCoefficient j (dyadicLambertPhase t) : ℂ)) := by
  constructor
  · intro j
    obtain ⟨C, hC⟩ :=
      (isBounded_range_fabiusSaddleMassCoefficient j).exists_norm_le
    apply IsBigO.of_bound C
    filter_upwards with t
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one] using
      hC (fabiusSaddleMassCoefficient j (dyadicLambertPhase t))
        ⟨dyadicLambertPhase t, rfl⟩
  · intro M
    cases M with
    | zero =>
        have hstrong :=
          fabiusSaddleKernelMass_dyadicLambert_sub_partialSum_isBigO F hF 0
        have hrate :
            (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ (0 + 1)) =O[atTop]
              (fun _t : ℝ => (1 : ℝ)) :=
          dyadicLambert_invPhasePow_isBigO_one 1
        have herr :
            (fun t : ℝ =>
              fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
                  (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
                  (fabiusLambertPhase ((2 : ℝ) ^ (-t))) - 1) =O[atTop]
                (fun _t : ℝ => (1 : ℝ)) := by
          simpa [fabiusSaddleMassCoefficient_zero] using hstrong.trans hrate
        have hone : (fun _t : ℝ => (1 : ℂ)) =O[atTop]
            (fun _t : ℝ => (1 : ℝ)) :=
          IsBigO.of_bound 1 (Filter.Eventually.of_forall fun _ => by simp)
        simpa [partialSum_zero] using herr.add hone
    | succ N =>
        simpa [partialSum, Complex.real_smul] using
          fabiusSaddleKernelMass_dyadicLambert_sub_partialSum_isBigO F hF N

end

end Fabius
