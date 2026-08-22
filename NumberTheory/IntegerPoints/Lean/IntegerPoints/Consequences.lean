import IntegerPoints.Wu

/-!
# Proved relations between the formal statements

The first proofs in the library: structural consequences that do not need
any analytic input.

* Exponent monotonicity: Wu's Theorem 1 implies the Zhai–Cao Theorem, which
  implies Nowak's bound.
* Wu's form of the unconditional bound (1.1) implies Zhai–Cao's printed
  form (1.2).
* Nowak's formula (Wu, §1) implies Zhai–Cao's Proposition 2.
* The regions `𝒜, ℬ, 𝒞, 𝒟` cover the square `M, N ≤ x^{1-2θ}`, so Wu's
  Propositions 1–4 together with his reduction yield Theorem 1.
-/

open Real Filter Asymptotics

namespace LeanProofs.IntegerPoints

/-- `x^p ≪ x^q` as `x → ∞` whenever `p ≤ q`. -/
theorem isBigO_rpow_rpow_of_le {p q : ℝ} (h : p ≤ q) :
    (fun x : ℝ => x ^ p) =O[atTop] fun x : ℝ => x ^ q := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := by linarith
  rw [one_mul, Real.norm_of_nonneg (rpow_nonneg hx0 _), Real.norm_of_nonneg (rpow_nonneg hx0 _)]
  exact rpow_le_rpow_of_exponent_le hx h

/-- A bound `Δ(x) ≪ x^{p+ε}` for all `ε > 0` implies the same with any
`q ≥ p`. -/
theorem primitiveCircleError_bound_mono {p q : ℝ} (h : p ≤ q)
    (hp : ∀ ε : ℝ, 0 < ε → primitiveCircleError =O[atTop] fun x : ℝ => x ^ (p + ε)) :
    ∀ ε : ℝ, 0 < ε → primitiveCircleError =O[atTop] fun x : ℝ => x ^ (q + ε) :=
  fun ε hε => (hp ε hε).trans (isBigO_rpow_rpow_of_le (by linarith))

/-- Wu's Theorem 1 (`221/608`) implies the Zhai–Cao Theorem (`11/30`). -/
theorem zhaiCao_theorem_of_wu_theorem1 : wu_theorem1 → zhaiCao_theorem :=
  fun h hRH => primitiveCircleError_bound_mono (by norm_num) (h hRH)

/-- The Zhai–Cao Theorem (`11/30`) implies Nowak's bound (`15/38`). -/
theorem nowak_of_zhaiCao_theorem : zhaiCao_theorem → nowak_primitiveCircleBound :=
  fun h hRH => primitiveCircleError_bound_mono (by norm_num) (h hRH)

/-- Wu's unconditional bound (with `(log log x)^{-1/5}`) implies the form
printed by Zhai–Cao (with `(log log x)^{-2/5}`). -/
theorem zhaiCao_unconditionalBound_of_wu : wu_unconditionalBound → zhaiCao_unconditionalBound := by
  rintro ⟨c, hc, h⟩
  refine ⟨c, hc, h.trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlog : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hlog0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlog
  have hll : 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hlog0).2 hlog
  have hll0 : 0 ≤ Real.log (Real.log x) := by linarith
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_le_exp]
  have hA : 0 ≤ c * Real.log x ^ ((3 : ℝ) / 5) := by positivity
  have key : Real.log (Real.log x) ^ (-(2 : ℝ) / 5) ≤
      (Real.log (Real.log x) ^ ((1 : ℝ) / 5))⁻¹ := by
    rw [← Real.rpow_neg hll0]
    exact rpow_le_rpow_of_exponent_le hll (by norm_num)
  calc -c * Real.log x ^ ((3 : ℝ) / 5) / Real.log (Real.log x) ^ ((1 : ℝ) / 5)
      = -(c * Real.log x ^ ((3 : ℝ) / 5) * (Real.log (Real.log x) ^ ((1 : ℝ) / 5))⁻¹) := by ring
    _ ≤ -(c * Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-(2 : ℝ) / 5)) := by
        apply neg_le_neg
        exact mul_le_mul_of_nonneg_left key hA
    _ = -c * Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-(2 : ℝ) / 5) := by ring

/-- Nowak's formula in Wu's form implies Zhai–Cao's Proposition 2. -/
theorem zhaiCao_prop2_of_wu_nowakFormula : wu_nowakFormula → zhaiCao_prop2 := by
  intro h hRH ε hε
  obtain ⟨C, hC⟩ := h hRH ε hε
  refine ⟨C, 2, fun x y hx hy1 hy2 => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have h1y : 1 ≤ y := le_trans (Real.one_le_rpow hx1 hε.le) hy1
  have hy : y < Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact lt_of_le_of_lt hy2 (Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith))
  have := hC x y hx h1y hy
  have hy0 : 0 ≤ y := by linarith
  calc |primitiveCircleError x - moebiusCircleErrorSum x y|
      ≤ C * (x ^ ((1 : ℝ) / 2 + ε) / y ^ ((1 : ℝ) / 2)) := this
    _ = C * (y ^ (-(1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2 + ε)) := by
        rw [neg_div, Real.rpow_neg hy0]; ring

/-- The regions `𝒜(θ), ℬ(θ), 𝒞(θ), 𝒟(θ)` cover the square
`0 < M, N ≤ x^{1-2θ}`; hence the bound (1.3) on each region gives it on the
square. -/
theorem RSumBoundOnSquare_of_regions (θ : ℝ)
    (hA : RSumBoundOn θ regionA) (hB : RSumBoundOn θ regionB)
    (hC : RSumBoundOn θ regionC) (hD : RSumBoundOn θ regionD) :
    RSumBoundOnSquare θ := by
  intro ε hε
  obtain ⟨CA, hA⟩ := hA ε hε
  obtain ⟨CB, hB⟩ := hB ε hε
  obtain ⟨CC, hC⟩ := hC ε hε
  obtain ⟨CD, hD⟩ := hD ε hε
  refine ⟨max (max CA CB) (max CC CD), fun x M N hx hM hMx hN hNx => ?_⟩
  have hxpos : 0 ≤ x ^ (θ - 1 / 4 + ε) := rpow_nonneg (by linarith) _
  have hCA : CA ≤ max (max CA CB) (max CC CD) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCB : CB ≤ max (max CA CB) (max CC CD) := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCC : CC ≤ max (max CA CB) (max CC CD) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCD : CD ≤ max (max CA CB) (max CC CD) := le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases hD' : x ^ (4 * θ - 1) ≤ M ^ 2 * N⁻¹
  · exact (hD x M N hx ⟨hM, hN, hMx, hNx, hD'⟩).trans (mul_le_mul_of_nonneg_right hCD hxpos)
  push Not at hD'
  by_cases hC' : N ≤ x ^ (3 - 8 * θ)
  · exact (hC x M N hx ⟨hM, hN, hMx, hNx, hC', hD'.le⟩).trans
      (mul_le_mul_of_nonneg_right hCC hxpos)
  push Not at hC'
  by_cases hA' : M ≤ x ^ (20 * θ - 7)
  · exact (hA x M N hx ⟨hM, hN, hA', hC'.le, hNx⟩).trans (mul_le_mul_of_nonneg_right hCA hxpos)
  push Not at hA'
  exact (hB x M N hx ⟨hM, hN, hA'.le, hMx, hC'.le, hNx⟩).trans
    (mul_le_mul_of_nonneg_right hCB hxpos)

/-- **Wu's Theorem 1 follows from Propositions 1–4 and the reduction of §1.** -/
theorem wu_theorem1_of_props (h1 : wu_prop1) (h2 : wu_prop2) (h3 : wu_prop3) (h4 : wu_prop4)
    (hred : wu_reductionToRSum) : wu_theorem1 := by
  intro hRH ε hε
  have hsq : RSumBoundOnSquare (221 / 608) :=
    RSumBoundOnSquare_of_regions _ (h1 _ (by norm_num) (by norm_num))
      (h2 _ (by norm_num) (by norm_num)) (h3 _ (by norm_num) (by norm_num)) h4
  exact hred _ (by norm_num) (by norm_num) hsq hRH ε hε

end LeanProofs.IntegerPoints
