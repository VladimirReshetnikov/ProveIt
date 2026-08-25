import FabiusFunction.DyadicSharpConditional
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Quantitative normalized Laplace-moment bounds

This module makes the sharp endpoint/Laplace comparison unconditional.  Its
key estimate is

`R_k(s)^2 ≤ s * ((4/s)^k k!)^2`, for `s ≥ 2`,

where `R_k=M_k/M_0` is the normalized tilted moment.  Hölder log-convexity
at the intermediate tilt `3s/4`, together with the exact dyadic product
factor between `s/2` and `s`, proves the estimate without any periodic
regularity input.  The cases `k=2,3,4` discharge both hypotheses of
`EndpointLaplaceComparison` and give an unconditional sharp dyadic formula
with its exact cumulant correction.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology ENNReal

namespace Fabius

private lemma unitLaplaceMoment_three_quarters_le_sqrt
    (s : ℝ) (hs : 0 ≤ s) :
    unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution
        (3 * s / 4) 0 ≤
      (unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution
          (s / 2) 0) ^ (1 / 2 : ℝ) *
        (unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution
          s 0) ^ (1 / 2 : ℝ) := by
  let μ : Measure ℝ :=
    ProbabilityRepresentation.weightedSumDistribution.restrict (Icc (0 : ℝ) 1)
  let f : ℝ → ℝ := fun x => Real.exp (-(s / 4) * x)
  let g : ℝ → ℝ := fun x => Real.exp (-(s / 2) * x)
  have hf_meas : AEStronglyMeasurable f μ := by
    exact (by fun_prop : Continuous f).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g μ := by
    exact (by fun_prop : Continuous g).aestronglyMeasurable
  have hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [hx.1]
  have hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [hx.1]
  have hf : MemLp f (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hf_meas 1 hf_bound
  have hg : MemLp g (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hg_meas 1 hg_bound
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le) hf hg
  simp only [unitLaplaceMoment, pow_zero, mul_one]
  change (∫ x, Real.exp (-(3 * s / 4) * x) ∂μ) ≤ _
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with x
    rw [← Real.exp_add]
    congr 1
    ring
  · congr 1
    · apply congrArg (fun y : ℝ => y ^ (1 / 2 : ℝ))
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_two, ← Real.exp_nat_mul]
      congr 1
      ring
    · apply congrArg (fun y : ℝ => y ^ (1 / 2 : ℝ))
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_two, ← Real.exp_nat_mul]
      congr 1
      ring

private lemma unitLaplaceMoment_three_quarters_sq_le
    (s : ℝ) (hs : 0 ≤ s) :
    unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution
          (3 * s / 4) 0 ^ 2 ≤
      unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution
          (s / 2) 0 *
        unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution
          s 0 := by
  let A := unitLaplaceMoment
    ProbabilityRepresentation.weightedSumDistribution (s / 2) 0
  let B := unitLaplaceMoment
    ProbabilityRepresentation.weightedSumDistribution s 0
  let C := unitLaplaceMoment
    ProbabilityRepresentation.weightedSumDistribution (3 * s / 4) 0
  have hA : 0 ≤ A := unitLaplaceMoment_nonneg _ _ _
  have hB : 0 ≤ B := unitLaplaceMoment_nonneg _ _ _
  have hC : 0 ≤ C := unitLaplaceMoment_nonneg _ _ _
  have h := unitLaplaceMoment_three_quarters_le_sqrt s hs
  change C ≤ A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) at h
  change C ^ 2 ≤ A * B
  calc
    C ^ 2 ≤ (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 := by
      exact (sq_le_sq₀ hC (by positivity)).2 h
    _ = A * B := by
      rw [mul_pow]
      rw [show (A ^ (1 / 2 : ℝ)) ^ 2 = A by
        simpa [one_div] using
          (Real.rpow_inv_natCast_pow hA (by norm_num : (2 : ℕ) ≠ 0))]
      rw [show (B ^ (1 / 2 : ℝ)) ^ 2 = B by
        simpa [one_div] using
          (Real.rpow_inv_natCast_pow hB (by norm_num : (2 : ℕ) ≠ 0))]

private lemma pow_mul_exp_neg_quarter_le
    (k : ℕ) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(s * x / 4)) ≤
      (4 / s) ^ k * (k.factorial : ℝ) := by
  let y : ℝ := s * x / 4
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hseries := Real.pow_div_factorial_le_exp y hy k
  have hmul := mul_le_mul_of_nonneg_right hseries (Real.exp_nonneg (-y))
  have hybound : y ^ k * Real.exp (-y) ≤ (k.factorial : ℝ) := by
    rw [div_mul_eq_mul_div] at hmul
    rw [← Real.exp_add] at hmul
    norm_num at hmul
    rwa [div_le_one hfac] at hmul
  have hscale : x = (4 / s) * y := by
    dsimp [y]
    field_simp
  rw [hscale, mul_pow]
  have hexp : -(s * ((4 / s) * y) / 4) = -y := by
    field_simp
  rw [hexp, mul_assoc]
  exact mul_le_mul_of_nonneg_left hybound (pow_nonneg (by positivity) k)

private lemma unitLaplaceMoment_le_three_quarters
    (k : ℕ) {s : ℝ} (hs : 0 < s) :
    unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution s k ≤
      ((4 / s) ^ k * (k.factorial : ℝ)) *
        unitLaplaceMoment ProbabilityRepresentation.weightedSumDistribution
          (3 * s / 4) 0 := by
  let μ := ProbabilityRepresentation.weightedSumDistribution
  let C : ℝ := (4 / s) ^ k * (k.factorial : ℝ)
  have hleft : IntegrableOn
      (fun x : ℝ => Real.exp (-s * x) * x ^ k) (Icc (0 : ℝ) 1) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    fun_prop
  have hright : IntegrableOn
      (fun x : ℝ => C * (Real.exp (-(3 * s / 4) * x) * x ^ 0))
      (Icc (0 : ℝ) 1) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    fun_prop
  unfold unitLaplaceMoment
  rw [← MeasureTheory.integral_const_mul]
  apply integral_mono_ae hleft hright
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [pow_zero, mul_one]
  have hsplit : Real.exp (-s * x) =
      Real.exp (-(3 * s / 4) * x) * Real.exp (-(s * x / 4)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  rw [mul_assoc, mul_comm (Real.exp (-(s * x / 4))) (x ^ k)]
  calc
    Real.exp (-(3 * s / 4) * x) *
          (x ^ k * Real.exp (-(s * x / 4))) ≤
        Real.exp (-(3 * s / 4) * x) * C := by
      exact mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_quarter_le k hs hx.1) (Real.exp_nonneg _)
    _ = C * Real.exp (-(3 * s / 4) * x) := by ring

/-- Midpoint log-convexity of the negative Laplace transform: for `0 ≤ s`,
`fabiusLaplaceMoment F 0 (3 * s / 4) ^ 2` is at most
`fabiusLaplaceMoment F 0 (s / 2) * fabiusLaplaceMoment F 0 s`.  Proved by
Cauchy--Schwarz between the tilts `s / 2` and `s`.  Requires `IsFabius F`. -/
lemma fabiusLaplaceMoment_three_quarters_sq_le
    (F : BoundedFabius) (hF : IsFabius F)
    (s : ℝ) (hs : 0 ≤ s) :
    fabiusLaplaceMoment F 0 (3 * s / 4) ^ 2 ≤
      fabiusLaplaceMoment F 0 (s / 2) * fabiusLaplaceMoment F 0 s := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using unitLaplaceMoment_three_quarters_sq_le s hs

/-- Trading `k` powers of the variable for a quarter of the tilt: for
`0 < s`, `fabiusLaplaceMoment F k s` is at most
`((4 / s) ^ k * k.factorial) * fabiusLaplaceMoment F 0 (3 * s / 4)`.
Requires `IsFabius F`. -/
lemma fabiusLaplaceMoment_le_three_quarters
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) {s : ℝ} (hs : 0 < s) :
    fabiusLaplaceMoment F k s ≤
      ((4 / s) ^ k * (k.factorial : ℝ)) *
        fabiusLaplaceMoment F 0 (3 * s / 4) := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using unitLaplaceMoment_le_three_quarters k hs

/-- Halving the tilt costs at most one factor of `s`: for `2 ≤ s`,
`fabiusLaplaceMoment F 0 (s / 2) ≤ s * fabiusLaplaceMoment F 0 s`.  The proof
uses the exact dyadic functional equation `proposition_two_real_formula`.
Requires `IsFabius F`. -/
lemma fabiusLaplaceMoment_zero_half_le_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 2 ≤ s) :
    fabiusLaplaceMoment F 0 (s / 2) ≤
      s * fabiusLaplaceMoment F 0 s := by
  have hs0 : 0 < s := by linarith
  have hhalf0 : 0 < s / 2 := by positivity
  have hA : 0 < fabiusLaplaceMoment F 0 (s / 2) :=
    fabiusLaplaceMoment_zero_pos F hF hhalf0
  have hehalf : Real.exp (-(s / 2)) ≤ 1 / 2 := by
    calc
      Real.exp (-(s / 2)) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le
  have hfactor : 1 / s ≤ (1 - Real.exp (-(s / 2))) / (s / 2) := by
    rw [le_div_iff₀ (by positivity : 0 < s / 2)]
    have hsne : s ≠ 0 := hs0.ne'
    field_simp
    nlinarith
  have hscale := proposition_two_real_formula F hF (-(s / 2))
  have harg : 2 * (-(s / 2)) = -s := by ring
  rw [harg] at hscale
  change fabiusLaplaceMoment F 0 s =
    expm1Div (-(s / 2)) * fabiusLaplaceMoment F 0 (s / 2) at hscale
  have hexpm1 : expm1Div (-(s / 2)) =
      (1 - Real.exp (-(s / 2))) / (s / 2) := by
    rw [expm1Div_of_ne (neg_ne_zero.mpr hhalf0.ne')]
    ring
  rw [hexpm1] at hscale
  have hmul := mul_le_mul_of_nonneg_right hfactor hA.le
  rw [← hscale] at hmul
  rw [div_mul_eq_mul_div] at hmul
  rw [div_le_iff₀ hs0] at hmul
  simpa [mul_comm] using hmul

/-- Normalization by the positive zeroth moment preserves nonnegativity. -/
lemma normalizedLaplaceMoment_nonneg
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) {s : ℝ} (hs : 0 < s) :
    0 ≤ normalizedLaplaceMoment F k s := by
  unfold normalizedLaplaceMoment
  exact div_nonneg (fabiusLaplaceMoment_nonneg F hF k s)
    (fabiusLaplaceMoment_zero_pos F hF hs).le

/-- A uniform square bound for every normalized tilted moment.  The loss of
one power of `s` comes from the exact dyadic factor, while log-convexity at
the intermediate tilt supplies its square root. -/
theorem normalizedLaplaceMoment_sq_le
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    normalizedLaplaceMoment F k s ^ 2 ≤
      s * (((4 / s) ^ k * (k.factorial : ℝ)) ^ 2) := by
  let A : ℝ := fabiusLaplaceMoment F 0 (s / 2)
  let B : ℝ := fabiusLaplaceMoment F 0 s
  let C : ℝ := (4 / s) ^ k * (k.factorial : ℝ)
  let D : ℝ := fabiusLaplaceMoment F 0 (3 * s / 4)
  let M : ℝ := fabiusLaplaceMoment F k s
  have hs0 : 0 < s := by linarith
  have hB : 0 < B := fabiusLaplaceMoment_zero_pos F hF hs0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := fabiusLaplaceMoment_nonneg F hF 0 _
  have hM : 0 ≤ M := fabiusLaplaceMoment_nonneg F hF k s
  have hMD : M ≤ C * D := fabiusLaplaceMoment_le_three_quarters F hF k hs0
  have hDsq : D ^ 2 ≤ A * B :=
    fabiusLaplaceMoment_three_quarters_sq_le F hF s hs0.le
  have hAB : A ≤ s * B := fabiusLaplaceMoment_zero_half_le_mul F hF hs
  have hraw : M ^ 2 ≤ s * C ^ 2 * B ^ 2 := by
    calc
      M ^ 2 ≤ (C * D) ^ 2 := (sq_le_sq₀ hM (mul_nonneg hC hD)).2 hMD
      _ = C ^ 2 * D ^ 2 := by ring
      _ ≤ C ^ 2 * (A * B) := by
        exact mul_le_mul_of_nonneg_left hDsq (sq_nonneg C)
      _ ≤ C ^ 2 * ((s * B) * B) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hAB hB.le) (sq_nonneg C)
      _ = s * C ^ 2 * B ^ 2 := by ring
  unfold normalizedLaplaceMoment
  change (M / B) ^ 2 ≤ s * C ^ 2
  rw [div_pow]
  rw [div_le_iff₀ (sq_pos_of_pos hB)]
  simpa [mul_assoc] using hraw

/-- The corresponding unsquared bound, uniform in the moment index. -/
theorem normalizedLaplaceMoment_le_sqrt
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    normalizedLaplaceMoment F k s ≤
      Real.sqrt s * ((4 / s) ^ k * (k.factorial : ℝ)) := by
  let C : ℝ := (4 / s) ^ k * (k.factorial : ℝ)
  have hs0 : 0 < s := by linarith
  have hR : 0 ≤ normalizedLaplaceMoment F k s :=
    normalizedLaplaceMoment_nonneg F hF k hs0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrhs : 0 ≤ Real.sqrt s * C :=
    mul_nonneg (Real.sqrt_nonneg s) hC
  apply (sq_le_sq₀ hR hrhs).mp
  calc
    normalizedLaplaceMoment F k s ^ 2 ≤ s * C ^ 2 :=
      normalizedLaplaceMoment_sq_le F hF k hs
    _ = Real.sqrt s ^ 2 * C ^ 2 := by rw [Real.sq_sqrt hs0.le]
    _ = (Real.sqrt s * C) ^ 2 := by ring

/-- Explicit second normalized moment bound on the ray `2 ≤ s`:
`normalizedLaplaceMoment F 2 s ^ 2 ≤ 1024 / s ^ 3`.  This is the `k = 2` case
of `normalizedLaplaceMoment_sq_le` after clearing denominators.  Requires
`IsFabius F`. -/
theorem normalizedLaplaceMoment_two_sq_le
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 2 ≤ s) :
    normalizedLaplaceMoment F 2 s ^ 2 ≤ 1024 / s ^ 3 := by
  have h := normalizedLaplaceMoment_sq_le F hF 2 hs
  have hs0 : 0 < s := by linarith
  have hsne : s ≠ 0 := hs0.ne'
  norm_num at h ⊢
  field_simp [hsne] at h ⊢
  nlinarith [sq_nonneg s]

/-- Explicit third normalized moment bound on the ray `2 ≤ s`:
`normalizedLaplaceMoment F 3 s ≤ 384 / s ^ 2`.  Obtained from the `k = 3`
case of `normalizedLaplaceMoment_sq_le` by taking square roots.  Requires
`IsFabius F`. -/
theorem normalizedLaplaceMoment_three_le
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 2 ≤ s) :
    normalizedLaplaceMoment F 3 s ≤ 384 / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hsq := normalizedLaplaceMoment_sq_le F hF 3 hs
  have hnonneg : 0 ≤ normalizedLaplaceMoment F 3 s :=
    normalizedLaplaceMoment_nonneg F hF 3 hs0
  have hbound0 : 0 ≤ 384 / s ^ 2 := by positivity
  apply (sq_le_sq₀ hnonneg hbound0).mp
  norm_num at hsq ⊢
  field_simp [hs0.ne'] at hsq ⊢
  nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]

/-- Explicit fourth normalized moment bound on the ray `2 ≤ s`:
`normalizedLaplaceMoment F 4 s ≤ 6144 / s ^ 3`.  Obtained from the `k = 4`
case of `normalizedLaplaceMoment_sq_le` by taking square roots.  Requires
`IsFabius F`. -/
theorem normalizedLaplaceMoment_four_le
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 2 ≤ s) :
    normalizedLaplaceMoment F 4 s ≤ 6144 / s ^ 3 := by
  have hs0 : 0 < s := by linarith
  have hsq := normalizedLaplaceMoment_sq_le F hF 4 hs
  have hnonneg : 0 ≤ normalizedLaplaceMoment F 4 s :=
    normalizedLaplaceMoment_nonneg F hF 4 hs0
  have hbound0 : 0 ≤ 6144 / s ^ 3 := by positivity
  apply (sq_le_sq₀ hnonneg hbound0).mp
  norm_num at hsq ⊢
  field_simp [hs0.ne'] at hsq ⊢
  nlinarith [sq_nonneg s, sq_nonneg (s ^ 3)]

/-- The square of `dyadicEndpointSecondOrder F` is `O(1/n)` along the
naturals; the proof uses the explicit constant `256` and the `k = 2` moment
bound above.  It supplies the `hsecond` hypothesis of
`dyadicEndpointLaplaceLogError_add_secondOrder_isBigO` and of
`log_fabius_dyadic_sub_cumulantMain_isBigO`, both invoked later in this file.
Requires `IsFabius F`. -/
theorem dyadicEndpointSecondOrder_sq_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => dyadicEndpointSecondOrder F n ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 256
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq := normalizedLaplaceMoment_two_sq_le F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn0)]
  unfold dyadicEndpointSecondOrder
  rw [← normalizedLaplaceMoment_two_eq_logSecond_add_first_sq]
  calc
    ((n : ℝ) / 2 * normalizedLaplaceMoment F 2 n) ^ 2 =
        (n : ℝ) ^ 2 / 4 * normalizedLaplaceMoment F 2 n ^ 2 := by ring
    _ ≤ (n : ℝ) ^ 2 / 4 * (1024 / (n : ℝ) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 256 * (n : ℝ)⁻¹ := by
      field_simp
      norm_num

/-- The combined higher-moment term `16 * (n * normalizedLaplaceMoment F 3 n
+ n ^ 2 * normalizedLaplaceMoment F 4 n)` is `O(1/n)` along the naturals; the
proof uses the explicit constant `104448` and the `k = 3, 4` bounds above.
It supplies the `hhigher` hypothesis of
`dyadicEndpointLaplaceLogError_add_secondOrder_isBigO` and of
`log_fabius_dyadic_sub_cumulantMain_isBigO`, both invoked later in this file.
Requires `IsFabius F`. -/
theorem dyadicHigherLaplaceMoments_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => 16 *
      ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 104448
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h3 := normalizedLaplaceMoment_three_le F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  have h4 := normalizedLaplaceMoment_four_le F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  have hR3 : 0 ≤ normalizedLaplaceMoment F 3 n :=
    normalizedLaplaceMoment_nonneg F hF 3 hn0
  have hR4 : 0 ≤ normalizedLaplaceMoment F 4 n :=
    normalizedLaplaceMoment_nonneg F hF 4 hn0
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 16 *
      ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn0)]
  calc
    16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤
      16 * ((n : ℝ) * (384 / (n : ℝ) ^ 2) +
        (n : ℝ) ^ 2 * (6144 / (n : ℝ) ^ 3)) := by gcongr
    _ = 104448 * (n : ℝ)⁻¹ := by
      field_simp
      norm_num

/-- The endpoint/Laplace logarithmic comparison is unconditional: the two
moment estimates required by the general transfer theorem follow from
log-convexity and the exact dyadic factor. -/
theorem dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_unconditional
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => dyadicEndpointLaplaceLogError n +
      dyadicEndpointSecondOrder F n) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) := by
  simpa [dyadicEndpointSecondOrder] using
    dyadicEndpointLaplaceLogError_add_secondOrder_isBigO F hF
      (by simpa [dyadicEndpointSecondOrder] using
        dyadicEndpointSecondOrder_sq_isBigO F hF)
      (dyadicHigherLaplaceMoments_isBigO F hF)

/-- Unconditional sharp dyadic formula with the exact cumulant correction. -/
theorem log_fabius_dyadic_sub_cumulantMain_isBigO_unconditional
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ =>
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpCumulantMain F n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) :=
  log_fabius_dyadic_sub_cumulantMain_isBigO F hF
    (dyadicEndpointSecondOrder_sq_isBigO F hF)
    (dyadicHigherLaplaceMoments_isBigO F hF)

end Fabius
