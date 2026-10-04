/-
# The series forms of the differential of the exponential (Theorem 5.2)

This file completes the formalization of Theorem 5.2 of the accompanying
article (`docs/combined`) begun in `BCH.Duhamel`:

* `dexp_apply_eq_tsum` (equation (5.5)):
  `(dexp)_A(H) = ∑ₙ 1/(n+1)! ∑_{i ≤ n} A^{n-i} H A^i`, obtained by differentiating
  the exponential series of `e^{A + tH}` termwise at `t = 0` and using the
  uniqueness of the derivative;
* `dexp_neg_apply`: `(dexp)_{-A}(H) = e^{-A} (dexp)_A(H) e^{-A}`, from the
  derivative of the inverse curve `t ↦ e^{-(A + tH)}`;
* `dexp_mul_exp_neg` (equation (5.7)):
  `(dexp)_A(H) e^{-A} = ∑ₙ 1/(n+1)! ad_A^n H = φ(-ad_A) H`.
-/
import BCH.Duhamel

open NormedSpace Finset Filter Topology

namespace BCH

section Series

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
lemma norm_pow_mul_mul_pow_le (f H : 𝔸) (a b : ℕ) :
    ‖f ^ a * H * f ^ b‖ ≤ ‖(1 : 𝔸)‖ ^ 2 * ‖f‖ ^ (a + b) * ‖H‖ := by
  calc ‖f ^ a * H * f ^ b‖ ≤ ‖f ^ a‖ * ‖H‖ * ‖f ^ b‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖(1 : 𝔸)‖ * ‖f‖ ^ a) * ‖H‖ * (‖(1 : 𝔸)‖ * ‖f‖ ^ b) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (norm_pow_le_norm_one_mul f a) (norm_nonneg _))
          (norm_pow_le_norm_one_mul f b) (norm_nonneg _) (by positivity)
    _ = ‖(1 : 𝔸)‖ ^ 2 * ‖f‖ ^ (a + b) * ‖H‖ := by rw [pow_add]; ring

omit [CompleteSpace 𝔸] in
/-- The derivative of the curve `t ↦ A + tH`. -/
lemma hasDerivAt_add_smul (A H : 𝔸) (t : 𝕂) : HasDerivAt (fun t : 𝕂 => A + t • H) H t := by
  simpa using ((hasDerivAt_id t).smul_const H).const_add A

/-- Termwise differentiation of the exponential series of `e^{A + tH}` at `t = 0`. -/
theorem hasDerivAt_exp_add_smul_series (A H : 𝔸) :
    (Summable fun n : ℕ =>
      ((n.factorial : 𝕂)⁻¹) • ∑ i ∈ range n, A ^ (n.pred - i) * H * A ^ i) ∧
    HasDerivAt (fun t : 𝕂 => exp (A + t • H))
      (∑' n : ℕ, ((n.factorial : 𝕂)⁻¹) • ∑ i ∈ range n, A ^ (n.pred - i) * H * A ^ i) 0 := by
  set D : Set 𝕂 := Metric.ball (0 : 𝕂) 1 with hD
  have hDopen : IsOpen D := Metric.isOpen_ball
  have hDconn : IsPreconnected D := (convex_ball (0 : 𝕂) 1).isPreconnected
  have h0D : (0 : 𝕂) ∈ D := Metric.mem_ball_self one_pos
  let f : ℕ → 𝕂 → 𝔸 := fun n t => ((n.factorial : 𝕂)⁻¹) • (A + t • H) ^ n
  let f' : ℕ → 𝕂 → 𝔸 := fun n t =>
    ((n.factorial : 𝕂)⁻¹) • ∑ i ∈ range n, (A + t • H) ^ (n.pred - i) * H * (A + t • H) ^ i
  have hf : ∀ n t, t ∈ D → HasDerivAt (f n) (f' n t) t := fun n t _ => by
    have h := ((hasDerivAt_add_smul A H t).pow' n).const_smul ((n.factorial : 𝕂)⁻¹)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun z => rfl)
  set b : ℝ := ‖A‖ + ‖H‖ + 1 with hb
  have hb1 : 1 ≤ b := by
    have := norm_nonneg A; have := norm_nonneg H; linarith
  let u : ℕ → ℝ := fun n => ‖(1 : 𝔸)‖ ^ 2 * ‖H‖ * ((2 * b) ^ n / (n.factorial : ℝ))
  have hu : Summable u := (Real.summable_pow_div_factorial (2 * b)).mul_left _
  have hf' : ∀ n t, t ∈ D → ‖f' n t‖ ≤ u n := by
    intro n t ht
    rw [hD, Metric.mem_ball, dist_zero_right] at ht
    have hAt : ‖A + t • H‖ ≤ b := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      have : ‖t‖ * ‖H‖ ≤ ‖H‖ := mul_le_of_le_one_left (norm_nonneg _) ht.le
      rw [hb]; linarith
    have hterm : ∀ i ∈ range n,
        ‖(A + t • H) ^ (n.pred - i) * H * (A + t • H) ^ i‖ ≤ ‖(1 : 𝔸)‖ ^ 2 * b ^ n * ‖H‖ := by
      intro i hi
      refine (norm_pow_mul_mul_pow_le _ _ _ _).trans ?_
      have hle : n.pred - i + i ≤ n := by
        rw [Nat.pred_eq_sub_one]
        have := mem_range.mp hi
        omega
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
        (norm_nonneg _)
      calc ‖A + t • H‖ ^ (n.pred - i + i) ≤ b ^ (n.pred - i + i) :=
            pow_le_pow_left₀ (norm_nonneg _) hAt _
        _ ≤ b ^ n := pow_le_pow_right₀ hb1 hle
    have hsum : ‖∑ i ∈ range n, (A + t • H) ^ (n.pred - i) * H * (A + t • H) ^ i‖ ≤
        n * (‖(1 : 𝔸)‖ ^ 2 * b ^ n * ‖H‖) := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_card_nsmul (range n) _ _ hterm
      rwa [card_range, nsmul_eq_mul] at this
    have hn2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    simp only [f', u]
    rw [norm_smul, norm_inv, RCLike.norm_natCast]
    calc ((n.factorial : ℕ) : ℝ)⁻¹ * ‖∑ i ∈ range n, (A + t • H) ^ (n.pred - i) * H * (A + t • H) ^ i‖
        ≤ ((n.factorial : ℕ) : ℝ)⁻¹ * (n * (‖(1 : 𝔸)‖ ^ 2 * b ^ n * ‖H‖)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ ((n.factorial : ℕ) : ℝ)⁻¹ * (2 ^ n * (‖(1 : 𝔸)‖ ^ 2 * b ^ n * ‖H‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn2 (by positivity))
            (by positivity)
      _ = ‖(1 : 𝔸)‖ ^ 2 * ‖H‖ * ((2 * b) ^ n / (n.factorial : ℝ)) := by
          rw [mul_pow]; ring
  have hf0 : Summable fun n => f n 0 := by
    simp only [f, zero_smul, add_zero]
    exact expSeries_summable' (𝕂 := 𝕂) A
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu hDopen hDconn hf hf' h0D hf0 h0D
  have hfun : (fun t => ∑' n, f n t) = fun t => exp (A + t • H) := by
    funext t; exact (exp_series_hasSum_exp' (𝕂 := 𝕂) (A + t • H)).tsum_eq
  rw [hfun] at hderiv
  have hf'0 : (fun n => f' n 0) = fun n : ℕ =>
      ((n.factorial : 𝕂)⁻¹) • ∑ i ∈ range n, A ^ (n.pred - i) * H * A ^ i := by
    funext n; simp only [f', zero_smul, add_zero]
  refine ⟨?_, ?_⟩
  · have := Summable.of_norm_bounded hu (fun n => hf' n 0 h0D)
    rwa [hf'0] at this
  · rw [← hf'0]; exact hderiv

/-- **Equation (5.5)**: `(dexp)_A(H) = ∑ₙ 1/(n+1)! ∑_{i ≤ n} A^{n-i} H A^i`, the double series
`∑_{p,q ≥ 0} A^p H A^q / (p+q+1)!` grouped by `n = p + q`. -/
theorem dexp_apply_eq_tsum (A H : 𝔸) :
    dexp 𝕂 A H =
      ∑' n : ℕ, (((n + 1).factorial : 𝕂)⁻¹) • ∑ i ∈ range (n + 1), A ^ (n - i) * H * A ^ i := by
  have h1 : HasDerivAt (fun t : 𝕂 => exp (A + t • H)) (dexp 𝕂 A H) 0 := by
    have := hasDerivAt_exp_comp (𝕂 := 𝕂) (hasDerivAt_add_smul A H 0)
    simpa using this
  obtain ⟨hsum, h2⟩ := hasDerivAt_exp_add_smul_series (𝕂 := 𝕂) A H
  rw [h1.unique h2, hsum.tsum_eq_zero_add]
  simp only [range_zero, sum_empty, smul_zero, zero_add, Nat.pred_succ]

/-- `(dexp)_{-A}(H) = e^{-A} (dexp)_A(H) e^{-A}`: the derivative of the inverse curve. -/
theorem dexp_neg_apply (A H : 𝔸) : dexp 𝕂 (-A) H = exp (-A) * dexp 𝕂 A H * exp (-A) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  -- derivative of `t ↦ e^{-(A + tH)}` in two ways
  have hcurve : HasDerivAt (fun t : 𝕂 => -(A + t • H)) (-H) 0 := (hasDerivAt_add_smul A H 0).neg
  have h1 : HasDerivAt (fun t : 𝕂 => exp (-(A + t • H))) (-dexp 𝕂 (-A) H) 0 := by
    have := hasDerivAt_exp_comp (𝕂 := 𝕂) hcurve
    simpa using this
  have h2 : HasDerivAt (fun t : 𝕂 => exp (A + t • H)) (dexp 𝕂 A H) 0 := by
    have := hasDerivAt_exp_comp (𝕂 := 𝕂) (hasDerivAt_add_smul A H 0)
    simpa using this
  -- the product `e^{-(A+tH)} e^{A+tH} = 1` has zero derivative
  have hprod : HasDerivAt (fun t : 𝕂 => exp (-(A + t • H)) * exp (A + t • H))
      (-dexp 𝕂 (-A) H * exp A + exp (-A) * dexp 𝕂 A H) 0 := by
    have h := h1.mul h2
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun z => rfl)).congr_deriv ?_
    simp
  have hone : (fun t : 𝕂 => exp (-(A + t • H)) * exp (A + t • H)) = fun _ => 1 := by
    funext t; exact exp_neg_mul_exp _
  rw [hone] at hprod
  have hzero : -dexp 𝕂 (-A) H * exp A + exp (-A) * dexp 𝕂 A H = 0 :=
    hprod.unique (hasDerivAt_const 0 (1 : 𝔸))
  -- solve for `dexp (-A) H`
  have : dexp 𝕂 (-A) H * exp A = exp (-A) * dexp 𝕂 A H := by
    rw [neg_mul] at hzero
    exact neg_add_eq_zero.mp hzero
  calc dexp 𝕂 (-A) H = dexp 𝕂 (-A) H * exp A * exp (-A) := by
        rw [mul_assoc, exp_mul_exp_neg, mul_one]
    _ = exp (-A) * dexp 𝕂 A H * exp (-A) := by rw [this]

/-- **Equation (5.7)**: `(dexp)_A(H) e^{-A} = ∑ₙ 1/(n+1)! ad_A^n H = φ(-ad_A) H`. -/
theorem dexp_mul_exp_neg (A H : 𝔸) :
    dexp 𝕂 A H * exp (-A) = ∑' n : ℕ, (((n + 1).factorial : 𝕂)⁻¹) • (ad 𝕂 A ^ n) H := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have h : dexp 𝕂 A H * exp (-A) = exp (- -A) * dexp 𝕂 (-A) H := by
    rw [dexp_neg_apply, neg_neg, ← mul_assoc, ← mul_assoc, exp_mul_exp_neg, one_mul]
  rw [h, exp_neg_mul_dexp]
  refine tsum_congr fun n => ?_
  rw [ad_neg_pow_apply, smul_smul, phiCoeff]
  congr 1
  rw [mul_comm ((-1 : 𝕂) ^ n), mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    mul_one]

end Series

end BCH
