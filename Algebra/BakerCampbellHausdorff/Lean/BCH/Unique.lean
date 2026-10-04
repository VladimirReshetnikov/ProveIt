/-
# Uniqueness of the small logarithm (Section 7.2)

This file formalizes the uniqueness statement of Section 7.2 of the accompanying
article (`docs/combined`, Proposition 7.4): for the Mercator logarithm
`log(1 + U) = ∑ₖ (-1)^{k-1} U^k / k` of `BCH.Log`,

* `mlog_exp_sub_one`: if `‖W‖ < log 2` then `log(e^W) = W`;
* `eq_tsum_bchHom_of_exp_eq`, `exp_eq_iff_eq_tsum_bchHom`: if `‖X‖ + ‖Y‖ < log 2`
  and `‖Z₀‖ < log 2`, then `e^{Z₀} = e^X e^Y` if and only if `Z₀ = ∑ₙ Zₙ(X, Y)`,
  the sum of the homogeneous BCH series.

The identity `log(e^W) = W` is proved by the zero-derivative device of the other
files: on the disc `‖t‖ < r`, `r > 1`, `r ‖W‖ < log 2`, the function
`L(t) = log(e^{tW})` is a series of powers of `U(t) = e^{tW} - 1`, all of whose
values commute with `U'(t) = W e^{tW}`; differentiating termwise gives
`L'(t) = (1 + U(t))⁻¹ U'(t) = W`, so `L(t) - tW` is constant, and it vanishes
at `t = 0`.
-/
import BCH.Remainder

open NormedSpace Finset Filter Topology

namespace BCH

section PowDeriv

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- Derivative of a power of a curve whose value commutes with its derivative. -/
lemma hasDerivAt_pow_succ_of_commute {U : 𝕂 → 𝔸} {U' : 𝔸} {s : 𝕂}
    (hU : HasDerivAt U U' s) (hc : Commute (U s) U') :
    ∀ n : ℕ, HasDerivAt (fun z => U z ^ (n + 1)) (((n + 1 : ℕ) : 𝕂) • (U s ^ n * U')) s
  | 0 => by simpa using hU
  | n + 1 => by
    have ih := hasDerivAt_pow_succ_of_commute hU hc n
    have h := ih.mul hU
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
    · have hcomm : U' * U s = U s * U' := hc.eq.symm
      rw [smul_mul_assoc, mul_assoc, hcomm, ← mul_assoc, ← pow_succ, Nat.cast_succ (n + 1),
        add_smul, one_smul]
    · simp [pow_succ]

end PowDeriv

section Unique

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- **The Mercator logarithm inverts the exponential on the ball `‖W‖ < log 2`**
(Section 7.2 of the article): `log(e^W) = W`. -/
theorem mlog_exp_sub_one {W : 𝔸} (hW : ‖W‖ < Real.log 2) : mlog 𝕂 (exp W - 1) = W := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- a disc of radius `r > 1` on which `r ‖W‖ < log 2`
  set r : ℝ := 2 * Real.log 2 / (Real.log 2 + ‖W‖) with hr
  have hr1 : 1 < r := by
    rw [hr, lt_div_iff₀ (by positivity)]; linarith
  have hrW : r * ‖W‖ < Real.log 2 := by
    rw [hr, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg W]
  have hr0 : 0 < r := by linarith
  set q : ℝ := Real.exp (r * ‖W‖) - 1 with hq
  have hq0 : 0 ≤ q := by
    have := Real.add_one_le_exp (r * ‖W‖)
    have : 0 ≤ r * ‖W‖ := by positivity
    linarith
  have hq1 : q < 1 := by
    have : Real.exp (r * ‖W‖) < 2 := by
      calc Real.exp (r * ‖W‖) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hrW
        _ = 2 := Real.exp_log two_pos
    linarith
  set B : Set 𝕂 := Metric.ball (0 : 𝕂) r with hB
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBconn : IsPreconnected B := (convex_ball (0 : 𝕂) r).isPreconnected
  have h0B : (0 : 𝕂) ∈ B := Metric.mem_ball_self hr0
  have h1B : (1 : 𝕂) ∈ B := by
    rw [hB, Metric.mem_ball, dist_zero_right, norm_one]; exact hr1
  -- the curve `U(t) = e^{tW} - 1`, its derivative, and the bounds on the disc
  let U : 𝕂 → 𝔸 := fun t => exp (t • W) - 1
  have hUderiv : ∀ t, HasDerivAt U (W * exp (t • W)) t := fun t =>
    (hasDerivAt_exp_smul_const' W t).sub_const 1
  have hUcomm : ∀ t, Commute (U t) (W * exp (t • W)) := fun t => by
    have h1 : Commute W (exp (t • W)) := ((Commute.refl W).smul_right t).exp_right
    have h2 : Commute (exp (t • W)) (W * exp (t • W)) := h1.symm.mul_right (Commute.refl _)
    exact h2.sub_left (Commute.one_left _)
  have hUnorm : ∀ t ∈ B, ‖U t‖ ≤ q := by
    intro t ht
    rw [hB, Metric.mem_ball, dist_zero_right] at ht
    have h := norm_exp_sub_one_le 𝕂 (t • W)
    rw [norm_smul] at h
    refine h.trans ?_
    rw [hq]
    have : ‖t‖ * ‖W‖ ≤ r * ‖W‖ := mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)
    linarith [Real.exp_le_exp.mpr this]
  have hEnorm : ∀ t ∈ B, ‖W * exp (t • W)‖ ≤ ‖W‖ * (‖(1 : 𝔸)‖ * Real.exp (r * ‖W‖)) := by
    intro t ht
    rw [hB, Metric.mem_ball, dist_zero_right] at ht
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (norm_exp_le 𝕂 _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_smul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _))
  -- the series `L(t) = log(1 + U(t))` and its termwise derivative
  let g : ℕ → 𝕂 → 𝔸 := fun n t => mlogTerm 𝕂 (U t) n
  let g' : ℕ → 𝕂 → 𝔸 := fun n t => (-1 : 𝕂) ^ n • (U t ^ n * (W * exp (t • W)))
  have hL : ∀ t, mlog 𝕂 (U t) = ∑' n, g n t := fun t => rfl
  have hg : ∀ n t, t ∈ B → HasDerivAt (g n) (g' n t) t := by
    intro n t _
    have h := (hasDerivAt_pow_succ_of_commute (hUderiv t) (hUcomm t) n).const_smul
      ((-1 : 𝕂) ^ n * ((n + 1 : ℕ) : 𝕂)⁻¹)
    refine h.congr_deriv ?_
    simp only [g', smul_smul]
    congr 1
    have hn : ((n + 1 : ℕ) : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  let u : ℕ → ℝ := fun n => ‖(1 : 𝔸)‖ * (‖W‖ * (‖(1 : 𝔸)‖ * Real.exp (r * ‖W‖))) * q ^ n
  have hu : Summable u :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hg' : ∀ n t, t ∈ B → ‖g' n t‖ ≤ u n := by
    intro n t ht
    simp only [g', u, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖U t ^ n * (W * exp (t • W))‖
        ≤ ‖U t ^ n‖ * ‖W * exp (t • W)‖ := norm_mul_le _ _
      _ ≤ (‖(1 : 𝔸)‖ * ‖U t‖ ^ n) * (‖W‖ * (‖(1 : 𝔸)‖ * Real.exp (r * ‖W‖))) :=
          mul_le_mul (norm_pow_le_norm_one_mul _ _) (hEnorm t ht) (norm_nonneg _)
            (by positivity)
      _ ≤ (‖(1 : 𝔸)‖ * q ^ n) * (‖W‖ * (‖(1 : 𝔸)‖ * Real.exp (r * ‖W‖))) := by
          gcongr
          exact hUnorm t ht
      _ = ‖(1 : 𝔸)‖ * (‖W‖ * (‖(1 : 𝔸)‖ * Real.exp (r * ‖W‖))) * q ^ n := by ring
  have hg0 : Summable fun n => g n 0 := by
    have : ∀ n, g n 0 = 0 := fun n => by
      simp [g, U, mlogTerm]
    simp only [this]
    exact summable_zero
  have hLderiv : ∀ t ∈ B, HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n t) t :=
    fun t ht => hasDerivAt_tsum_of_isPreconnected hu hBopen hBconn hg hg' h0B hg0 ht
  -- the derivative is `W`
  have hD : ∀ t ∈ B, ∑' n, g' n t = W := by
    intro t ht
    have hx : ‖-(U t)‖ < 1 := by rw [norm_neg]; exact (hUnorm t ht).trans_lt hq1
    have hgeom : (∑' n : ℕ, (-(U t)) ^ n) * (1 - -(U t)) = 1 := geom_series_mul_neg _ hx
    have hsum : Summable fun n : ℕ => (-(U t)) ^ n := summable_geometric_of_norm_lt_one hx
    have hterm : ∀ n : ℕ, g' n t = (-(U t)) ^ n * (exp (t • W) * W) := by
      intro n
      simp only [g']
      rw [← neg_one_smul 𝕂 (U t), smul_pow, smul_mul_assoc,
        (((Commute.refl W).smul_right t).exp_right).eq]
    have hE : 1 - -(U t) = exp (t • W) := by simp [U]
    calc ∑' n, g' n t = (∑' n : ℕ, (-(U t)) ^ n) * (exp (t • W) * W) := by
          simp only [hterm]
          rw [hsum.tsum_mul_right]
      _ = ((∑' n : ℕ, (-(U t)) ^ n) * (1 - -(U t))) * W := by rw [hE, mul_assoc]
      _ = W := by rw [hgeom, one_mul]
  -- `h(t) = L(t) - t W` has zero derivative on the disc
  let h : 𝕂 → 𝔸 := fun t => (∑' n, g n t) - t • W
  have hderiv : ∀ t ∈ B, HasDerivAt h 0 t := by
    intro t ht
    have h1 := (hLderiv t ht).sub ((hasDerivAt_id t).smul_const W)
    refine h1.congr_deriv ?_
    rw [hD t ht, one_smul, sub_self]
  have hdiff : DifferentiableOn 𝕂 h B :=
    fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  have hd0 : B.EqOn (deriv h) 0 := fun t ht => (hderiv t ht).deriv
  have hconst : h 1 = h 0 := hBopen.is_const_of_deriv_eq_zero hBconn hdiff hd0 h1B h0B
  have hh0 : h 0 = 0 := by
    have : (∑' n, g n 0) = 0 := by
      have : ∀ n, g n 0 = 0 := fun n => by simp [g, U, mlogTerm]
      simp only [this, tsum_zero]
    simp only [h, this, zero_smul, sub_zero]
  have hh1 : h 1 = mlog 𝕂 (exp W - 1) - W := by
    simp only [h, one_smul]
    rw [← hL]
    simp [U]
  rw [hh1, hh0] at hconst
  exact sub_eq_zero.mp hconst

/-- **Uniqueness of the BCH logarithm** (Section 7.2 of the article): if `‖X‖ + ‖Y‖ < log 2`,
`‖Z₀‖ < log 2` and `e^{Z₀} = e^X e^Y`, then `Z₀` is the sum of the homogeneous BCH series. -/
theorem eq_tsum_bchHom_of_exp_eq {X Y Z₀ : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2)
    (hZ : ‖Z₀‖ < Real.log 2) (h : exp Z₀ = exp X * exp Y) :
    Z₀ = ∑' n, bchHom 𝕂 X Y n := by
  rw [tsum_bchHom_eq_mlog hs, ← h, mlog_exp_sub_one hZ]

/-- **The BCH series as the unique small logarithm**: for `‖X‖ + ‖Y‖ < log 2` and
`‖Z₀‖ < log 2`, `e^{Z₀} = e^X e^Y` if and only if `Z₀ = ∑ₙ Zₙ(X, Y)`. -/
theorem exp_eq_iff_eq_tsum_bchHom {X Y Z₀ : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2)
    (hZ : ‖Z₀‖ < Real.log 2) :
    exp Z₀ = exp X * exp Y ↔ Z₀ = ∑' n, bchHom 𝕂 X Y n :=
  ⟨eq_tsum_bchHom_of_exp_eq hs hZ, fun h => by rw [h]; exact exp_tsum_bchHom hs⟩

end Unique

end BCH
