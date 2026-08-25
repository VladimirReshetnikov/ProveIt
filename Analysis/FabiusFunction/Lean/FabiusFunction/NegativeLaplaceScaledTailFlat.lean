import FabiusFunction.NegativeLaplaceAllOrderJets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Flatness of all scaled forward-tail derivatives

This module supplies the quantitative remainder behind the exact ordinary
negative-Laplace jets.  Every positive-order forward-tail summand admits a
uniform polynomial-times-exponential bound on `[1,∞)`.  After scaling the
`(n+1)`st derivative by `s^(n+1)`, the dyadic sum is still exponentially
small.  On `s = 2^t` it is little-o of every real power of the radius; the
previous natural inverse-power `O` estimate is retained as a compatibility
corollary.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius

private lemma pow_mul_exp_neg_le_exp_half
    (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ k * Real.exp (-y) ≤
      (2 : ℝ) ^ k * k.factorial * Real.exp (-(y / 2)) := by
  have hbase := Real.pow_div_factorial_le_exp (y / 2)
    (by positivity : 0 ≤ y / 2) k
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hpow : (y / 2) ^ k ≤ Real.exp (y / 2) * k.factorial := by
    rw [div_le_iff₀ hfac] at hbase
    simpa [mul_comm] using hbase
  have hscale : y ^ k = (2 : ℝ) ^ k * (y / 2) ^ k := by
    rw [div_pow]
    field_simp
  calc
    y ^ k * Real.exp (-y) =
        (2 : ℝ) ^ k * (y / 2) ^ k * Real.exp (-y) := by rw [hscale]
    _ ≤ (2 : ℝ) ^ k *
        (Real.exp (y / 2) * k.factorial) * Real.exp (-y) := by
      gcongr
    _ = (2 : ℝ) ^ k * k.factorial *
        (Real.exp (y / 2) * Real.exp (-y)) := by ring
    _ = (2 : ℝ) ^ k * k.factorial * Real.exp (-(y / 2)) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Uniform pointwise exponential majorant for every positive-order
forward-tail summand. -/
theorem exists_norm_negativeLaplaceForwardTermDeriv_succ_le_exp
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 1 ≤ s → ∀ m : ℕ,
      ‖negativeLaplaceForwardTermDeriv (k + 1) s m‖ ≤
        C * (((2 : ℝ) ^ m) ^ (k + 1) *
          Real.exp (-(s * (2 : ℝ) ^ m))) := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_bound_abs_forwardDerivativeQuotientPolynomial k
  let d := 1 - Real.exp (-1)
  have hd : 0 < d := by
    dsimp [d]
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  refine ⟨B / d ^ (k + 1),
    div_nonneg hB0 (pow_nonneg hd.le _), ?_⟩
  intro s hs m
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  let A := (2 : ℝ) ^ m
  let z := Real.exp (-(s * A))
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    exact one_le_pow₀ (by norm_num)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hs0.le hA.le))
  have hpoly :
      |(forwardDerivativeQuotientPolynomial k).eval z| ≤ B :=
    hB z ⟨hz0, hz1⟩
  have hzone : z ≤ Real.exp (-1) := by
    dsimp [z]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul hs hA1 (by norm_num : (0 : ℝ) ≤ 1) hs0.le]
  have hden : d ≤ 1 - z := by
    dsimp [d]
    exact sub_le_sub_left hzone 1
  have hdenz : 0 < 1 - z := by
    rw [sub_pos, ← Real.exp_zero]
    dsimp [z]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos hs0 hA))
  rw [negativeLaplaceForwardTermDeriv_succ]
  dsimp only
  change ‖A ^ (k + 1) * z *
      (forwardDerivativeQuotientPolynomial k).eval z /
        (1 - z) ^ (k + 1)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_pos (pow_pos hA _), abs_of_nonneg hz0,
    abs_pow, abs_of_pos hdenz]
  calc
    A ^ (k + 1) * z *
          |(forwardDerivativeQuotientPolynomial k).eval z| /
          (1 - z) ^ (k + 1) ≤
        A ^ (k + 1) * z * B / d ^ (k + 1) := by
      apply div_le_div₀
      · positivity
      · gcongr
      · positivity
      · exact pow_le_pow_left₀ hd.le hden _
    _ = (B / d ^ (k + 1)) *
        (A ^ (k + 1) * z) := by ring

/-- Every scaled forward-tail derivative is exponentially small in its
positive argument, uniformly on `[1,∞)`. -/
theorem exists_norm_scaled_negativeLaplaceForwardTailDeriv_le_exp
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 1 ≤ s →
      ‖s ^ (k + 1) * negativeLaplaceForwardTailDeriv (k + 1) s‖ ≤
        C * Real.exp (-(s / 2)) := by
  obtain ⟨C, hC0, hterm⟩ :=
    exists_norm_negativeLaplaceForwardTermDeriv_succ_le_exp k
  let D : ℝ := (2 : ℝ) ^ (k + 1) * (k + 1).factorial
  let r0 : ℝ := Real.exp (-(1 / 2 : ℝ))
  let K : ℝ := C * D / (1 - r0)
  have hr00 : 0 ≤ r0 := by dsimp [r0]; positivity
  have hr01 : r0 < 1 := by
    dsimp [r0]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hK0 : 0 ≤ K := by
    dsimp [K, D]
    positivity
  refine ⟨K, hK0, ?_⟩
  intro s hs
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  let r : ℝ := Real.exp (-(s / 2))
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrr0 : r ≤ r0 := by
    dsimp [r, r0]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hr1 : r < 1 := hrr0.trans_lt hr01
  have hsummable : Summable (fun m : ℕ => r ^ (m + 1)) := by
    simpa [pow_succ'] using
      (summable_geometric_of_lt_one hr0 hr1).mul_left r
  have htailSummable :=
    summable_negativeLaplaceForwardTermDeriv (k + 1) s hs0
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs0.le _)]
  calc
    s ^ (k + 1) * ‖negativeLaplaceForwardTailDeriv (k + 1) s‖ ≤
        ∑' m : ℕ,
          s ^ (k + 1) *
            ‖negativeLaplaceForwardTermDeriv (k + 1) s m‖ := by
      unfold negativeLaplaceForwardTailDeriv
      rw [tsum_mul_left]
      gcongr
      exact norm_tsum_le_tsum_norm htailSummable.norm
    _ ≤ ∑' m : ℕ, C * D * r ^ (m + 1) := by
      apply Summable.tsum_le_tsum
      · intro m
        let A : ℝ := (2 : ℝ) ^ m
        have hA : 0 < A := by dsimp [A]; positivity
        have hraw := hterm s hs m
        have hnonneg : 0 ≤ C * (A ^ (k + 1) *
            Real.exp (-(s * A))) := by positivity
        have hscaled :
            s ^ (k + 1) *
                ‖negativeLaplaceForwardTermDeriv (k + 1) s m‖ ≤
              C * ((s * A) ^ (k + 1) *
                Real.exp (-(s * A))) := by
          calc
            s ^ (k + 1) *
                ‖negativeLaplaceForwardTermDeriv (k + 1) s m‖ ≤
                s ^ (k + 1) *
                  (C * (A ^ (k + 1) * Real.exp (-(s * A)))) := by
              gcongr
            _ = C * ((s * A) ^ (k + 1) *
                Real.exp (-(s * A))) := by ring
        have hpoly := pow_mul_exp_neg_le_exp_half (k + 1)
          (show 0 ≤ s * A by positivity)
        calc
          s ^ (k + 1) *
                ‖negativeLaplaceForwardTermDeriv (k + 1) s m‖ ≤
              C * ((s * A) ^ (k + 1) *
                Real.exp (-(s * A))) := hscaled
          _ ≤ C * (D * Real.exp (-((s * A) / 2))) := by
            gcongr
          _ ≤ C * D * r ^ (m + 1) := by
            have hmA : ((m + 1 : ℕ) : ℝ) ≤ A := by
              dsimp [A]
              have hnat : m + 1 ≤ 2 ^ m :=
                Nat.succ_le_of_lt Nat.lt_two_pow_self
              exact_mod_cast hnat
            have hexp : Real.exp (-((s * A) / 2)) ≤
                Real.exp (-(s / 2)) ^ (m + 1) := by
              rw [← Real.exp_nat_mul]
              apply Real.exp_le_exp.mpr
              nlinarith
            have hD0 : 0 ≤ D := by dsimp [D]; positivity
            calc
              C * (D * Real.exp (-((s * A) / 2))) ≤
                  C * (D * r ^ (m + 1)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hexp hD0) hC0
              _ = C * D * r ^ (m + 1) := by ring
      · exact (htailSummable.norm.mul_left (s ^ (k + 1)))
      · exact hsummable.mul_left (C * D)
    _ = C * D * (r / (1 - r)) := by
      rw [show (fun m : ℕ => C * D * r ^ (m + 1)) =
          fun m : ℕ => (C * D) * r ^ (m + 1) by rfl,
        tsum_mul_left]
      rw [show (fun m : ℕ => r ^ (m + 1)) = fun m => r * r ^ m by
        funext m
        rw [pow_succ']]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      simp only [div_eq_mul_inv]
    _ ≤ K * r := by
      have hden0 : 0 < 1 - r0 := sub_pos.mpr hr01
      have hden : 1 - r0 ≤ 1 - r := sub_le_sub_left hrr0 1
      dsimp only [K]
      rw [show C * D / (1 - r0) * r =
          (C * D) * (r / (1 - r0)) by ring]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hr0 hden0 hden)
        (mul_nonneg hC0 (by dsimp [D]; positivity))
    _ = K * Real.exp (-(s / 2)) := rfl

/-- Quantitative dyadic-orbit form of the scaled tail estimate.  Unlike the
asymptotic wrapper below, this exposes a single constant valid for every
nonnegative logarithmic scale. -/
theorem exists_norm_negativeLaplaceForwardScaledJet_le_exp
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t →
      ‖negativeLaplaceForwardScaledJet n t‖ ≤
        C * Real.exp (-(1 / 2 : ℝ) * ((2 : ℝ) ^ t)) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_scaled_negativeLaplaceForwardTailDeriv_le_exp n
  refine ⟨C, hC0, ?_⟩
  intro t ht
  have hs : (1 : ℝ) ≤ (2 : ℝ) ^ t := by
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
  simpa [negativeLaplaceForwardScaledJet, div_eq_mul_inv, mul_comm] using
    hC ((2 : ℝ) ^ t) hs

/-- Every scaled forward-tail derivative has double-exponential decay along
the dyadic logarithmic orbit. -/
theorem negativeLaplaceForwardScaledJet_isBigO_exp
    (n : ℕ) :
    negativeLaplaceForwardScaledJet n =O[atTop]
      (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * ((2 : ℝ) ^ t))) := by
  obtain ⟨C, _hC0, hC⟩ :=
    exists_norm_negativeLaplaceForwardScaledJet_le_exp n
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hC t ht

/-- Double-exponential decay beats every real power of the dyadic radius.
No sign restriction on the power is needed. -/
theorem negativeLaplaceForwardScaledJet_isLittleO_rpow_neg
    (n : ℕ) (p : ℝ) :
    negativeLaplaceForwardScaledJet n =o[atTop]
      (fun t : ℝ => ((2 : ℝ) ^ t) ^ (-p)) := by
  have hpow : Tendsto (fun t : ℝ => (2 : ℝ) ^ t) atTop atTop := by
    have hlin : Tendsto (fun t : ℝ => Real.log 2 * t) atTop atTop :=
      tendsto_id.const_mul_atTop (Real.log_pos (by norm_num))
    have hex := Real.tendsto_exp_atTop.comp hlin
    simpa only [Function.comp_def,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] using hex
  have hexp :
      (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * ((2 : ℝ) ^ t))) =o[atTop]
        (fun t : ℝ => ((2 : ℝ) ^ t) ^ (-p)) := by
    simpa only [Function.comp_def] using
      (isLittleO_exp_neg_mul_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 2) (-p)).comp_tendsto hpow
  exact (negativeLaplaceForwardScaledJet_isBigO_exp n).trans_isLittleO hexp

/-- In particular, every scaled forward-tail jet tends to zero. -/
theorem negativeLaplaceForwardScaledJet_tendsto_zero (n : ℕ) :
    Tendsto (negativeLaplaceForwardScaledJet n) atTop (nhds 0) := by
  apply (isLittleO_const_iff (one_ne_zero : (1 : ℝ) ≠ 0)).mp
  simpa using negativeLaplaceForwardScaledJet_isLittleO_rpow_neg n 0

/-- Arbitrary-filter transfer of the all-real-power flatness estimate. -/
theorem negativeLaplaceForwardScaledJet_comp_isLittleO_rpow_neg
    {α : Type*} (l : Filter α) (phase : α → ℝ)
    (hphase : Tendsto phase l atTop) (n : ℕ) (p : ℝ) :
    (fun x => negativeLaplaceForwardScaledJet n (phase x)) =o[l]
      (fun x => ((2 : ℝ) ^ phase x) ^ (-p)) := by
  simpa only [Function.comp_def] using
    (negativeLaplaceForwardScaledJet_isLittleO_rpow_neg n p).comp_tendsto hphase

/-- Natural-power form of the all-real-power flatness estimate. -/
theorem negativeLaplaceForwardScaledJet_isLittleO_inv_rpow
    (n N : ℕ) :
    negativeLaplaceForwardScaledJet n =o[atTop]
      (fun t : ℝ => (((2 : ℝ) ^ t)⁻¹) ^ N) := by
  apply (negativeLaplaceForwardScaledJet_isLittleO_rpow_neg n (N : ℝ)).congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards with t
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

/-- The scaled derivative tail is flat to every inverse power of the dyadic
radius. -/
theorem negativeLaplaceForwardScaledJet_isBigO_inv_rpow
    (n N : ℕ) :
    negativeLaplaceForwardScaledJet n =O[atTop]
      (fun t : ℝ => (((2 : ℝ) ^ t)⁻¹) ^ N) := by
  exact (negativeLaplaceForwardScaledJet_isLittleO_inv_rpow n N).isBigO

end Fabius
