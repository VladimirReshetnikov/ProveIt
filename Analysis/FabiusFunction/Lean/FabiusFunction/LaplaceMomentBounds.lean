import FabiusFunction.DyadicSharpConditional
import FabiusFunction.UnitLaplaceMomentBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quantitative normalized Laplace-moment bounds

This module makes the sharp endpoint/Laplace comparison unconditional.  Its
key estimate is

`R_k(s)^2 ≤ s * ((4/s)^k k!)^2`, for `s ≥ 2`,

where `R_k=M_k/M_0` is the normalized tilted moment.  Hölder log-convexity
at the intermediate tilt `3s/4`, together with the exact dyadic product
factor between `s/2` and `s`, proves the estimate without any periodic
regularity input.  Before imposing the positive-scale hypotheses needed by
those quantitative bounds, the module records that every `R_k(s)` is
nonnegative for every real tilt.  The cases `k=2,3,4` discharge both
hypotheses of `EndpointLaplaceComparison` and give an unconditional sharp
dyadic formula
with its exact cumulant correction.  The measure-generic Cauchy--Schwarz and
factorial-absorption engine lives in `UnitLaplaceMomentBounds`; this module
specializes it to Fabius moments.  Pointwise, the two transfer inputs are
at most `256/n` and `104448/n` for `n ≥ 2`.  Consequently, for
`n ≥ 224043` the endpoint error is at most `209408/n`, and the complete
cumulant logarithmic error is at most `2512945/(12n)`.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace Fabius

set_option linter.unusedVariables false in
/-- Midpoint log-convexity of the negative Laplace transform: for `0 ≤ s`,
`fabiusLaplaceMoment F 0 (3 * s / 4) ^ 2` is at most
`fabiusLaplaceMoment F 0 (s / 2) * fabiusLaplaceMoment F 0 s`.  Proved by
Cauchy--Schwarz between the tilts `s / 2` and `s`.  The hypothesis `0 ≤ s`
is retained for API compatibility; the generic midpoint theorem is valid at
every real tilt.  Requires `IsFabius F`. -/
lemma fabiusLaplaceMoment_three_quarters_sq_le
    (F : BoundedFabius) (hF : IsFabius F)
    (s : ℝ) (hs : 0 ≤ s) :
    fabiusLaplaceMoment F 0 (3 * s / 4) ^ 2 ≤
      fabiusLaplaceMoment F 0 (s / 2) * fabiusLaplaceMoment F 0 s := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using
    unitLaplaceMoment_three_quarters_sq_le_all
      ProbabilityRepresentation.weightedSumDistribution s

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
      F hF] using
    unitLaplaceMoment_le_three_quarters
      ProbabilityRepresentation.weightedSumDistribution k hs

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

/-- Every normalized tilted Fabius moment is nonnegative at every real tilt.
Its raw numerator is nonnegative and its zeroth-moment denominator is strictly
positive, so their quotient is nonnegative. -/
lemma normalizedLaplaceMoment_nonneg_all
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (s : ℝ) :
    0 ≤ normalizedLaplaceMoment F k s := by
  unfold normalizedLaplaceMoment
  exact div_nonneg (fabiusLaplaceMoment_nonneg F hF k s)
    (fabiusLaplaceMoment_zero_pos_all F hF s).le

/-- Positive-scale compatibility form of
`normalizedLaplaceMoment_nonneg_all`. -/
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

/-- Effective pointwise form of `dyadicEndpointSecondOrder_sq_isBigO`.
The square of the second endpoint correction is at most `256 / n` on
`2 ≤ n`. -/
theorem dyadicEndpointSecondOrder_sq_le
    (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} (hn : 2 ≤ n) :
    dyadicEndpointSecondOrder F n ^ 2 ≤ 256 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq := normalizedLaplaceMoment_two_sq_le F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  unfold dyadicEndpointSecondOrder
  rw [← normalizedLaplaceMoment_two_eq_logSecond_add_first_sq]
  calc
    ((n : ℝ) / 2 * normalizedLaplaceMoment F 2 n) ^ 2 =
        (n : ℝ) ^ 2 / 4 * normalizedLaplaceMoment F 2 n ^ 2 := by ring
    _ ≤ (n : ℝ) ^ 2 / 4 * (1024 / (n : ℝ) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 256 / (n : ℝ) := by
      field_simp
      norm_num

/-- The square of `dyadicEndpointSecondOrder F` is `O(1/n)` along the
naturals.  This compatibility form is an immediate asymptotic wrapper around
the stronger pointwise estimate `dyadicEndpointSecondOrder_sq_le`. -/
theorem dyadicEndpointSecondOrder_sq_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => dyadicEndpointSecondOrder F n ^ 2) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 256
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn0)]
  simpa [div_eq_mul_inv] using dyadicEndpointSecondOrder_sq_le F hF hn

/-- Effective pointwise form of `dyadicHigherLaplaceMoments_isBigO`.
The combined third- and fourth-moment transfer term is at most `104448 / n`
on `2 ≤ n`. -/
theorem dyadicHigherLaplaceMoments_le
    (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} (hn : 2 ≤ n) :
    16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
      (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤
        104448 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h3 := normalizedLaplaceMoment_three_le F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  have h4 := normalizedLaplaceMoment_four_le F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  calc
    16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤
      16 * ((n : ℝ) * (384 / (n : ℝ) ^ 2) +
        (n : ℝ) ^ 2 * (6144 / (n : ℝ) ^ 3)) := by gcongr
    _ = 104448 / (n : ℝ) := by
      field_simp
      norm_num

/-- The combined higher-moment term
`16 * (n * normalizedLaplaceMoment F 3 n + n ^ 2 *
normalizedLaplaceMoment F 4 n)` is `O(1/n)` along the naturals.  This
compatibility form wraps the stronger pointwise estimate
`dyadicHigherLaplaceMoments_le`. -/
theorem dyadicHigherLaplaceMoments_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => 16 *
      ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 104448
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR3 : 0 ≤ normalizedLaplaceMoment F 3 n :=
    normalizedLaplaceMoment_nonneg F hF 3 hn0
  have hR4 : 0 ≤ normalizedLaplaceMoment F 4 n :=
    normalizedLaplaceMoment_nonneg F hF 4 hn0
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 16 *
      ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn0)]
  simpa [div_eq_mul_inv] using dyadicHigherLaplaceMoments_le F hF hn

/-- Fully effective unconditional endpoint/Laplace comparison.  The threshold
`224043` makes the two pointwise moment bounds imply the radius-`1/2`
logarithm-chart hypothesis; no optimality for the actual error is claimed. -/
theorem abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_unconditional
    (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} (hn : 224043 ≤ n) :
    |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| ≤
      209408 / (n : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hn0_nat : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn0_nat
  have hnr : (224043 : ℝ) ≤ n := by exact_mod_cast hn
  have hsecond := dyadicEndpointSecondOrder_sq_le F hF hn2
  have hhigher := dyadicHigherLaplaceMoments_le F hF hn2
  have hsecond_nonneg : 0 ≤ dyadicEndpointSecondOrder F n := by
    unfold dyadicEndpointSecondOrder
    rw [← normalizedLaplaceMoment_two_eq_logSecond_add_first_sq]
    exact mul_nonneg (by positivity)
      (normalizedLaplaceMoment_nonneg F hF 2 hn0)
  have hmargin_nonneg : 0 ≤ 1 / 2 - 104448 / (n : ℝ) := by
    rw [sub_nonneg, div_le_iff₀ hn0]
    norm_num
    linarith
  have hmargin_sq :
      256 / (n : ℝ) ≤ (1 / 2 - 104448 / (n : ℝ)) ^ 2 := by
    rw [div_le_iff₀ hn0]
    field_simp [hn0.ne']
    nlinarith [sq_nonneg ((n : ℝ) - 224043)]
  have hsecond_margin :
      |dyadicEndpointSecondOrder F n| ≤ 1 / 2 - 104448 / (n : ℝ) := by
    rw [abs_of_nonneg hsecond_nonneg]
    exact (sq_le_sq₀ hsecond_nonneg hmargin_nonneg).mp
      (hsecond.trans hmargin_sq)
  have hsmall :
      |dyadicEndpointSecondOrder F n| +
        16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
          (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤ 1 / 2 := by
    linarith
  have hlog := abs_dyadicEndpointLaplaceLogError_add_secondOrder_le
    F hF n (by omega) (by
      simpa [dyadicEndpointSecondOrder] using hsmall)
  calc
    |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| ≤
        2 * dyadicEndpointSecondOrder F n ^ 2 +
          2 * (16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
            (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)) := by
      simpa [dyadicEndpointSecondOrder] using hlog
    _ ≤ 2 * (256 / (n : ℝ)) + 2 * (104448 / (n : ℝ)) := by gcongr
    _ = 209408 / (n : ℝ) := by ring

/-- Asymptotic compatibility form of the fully effective unconditional
endpoint/Laplace comparison. -/
theorem dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_unconditional
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => dyadicEndpointLaplaceLogError n +
      dyadicEndpointSecondOrder F n) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound 209408
  filter_upwards [eventually_atTop.2 ⟨224043, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn0)]
  simpa [div_eq_mul_inv] using
    abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_unconditional F hF hn

/-- Effective cumulant-form dyadic logarithmic estimate, combining the
endpoint bound with the `4/n` negative-Laplace tail estimate and the
`1/(12n)` Stirling remainder. -/
theorem abs_log_fabius_dyadic_sub_cumulantMain_le_unconditional
    (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} (hn : 224043 ≤ n) :
    |Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpCumulantMain F n| ≤ 2512945 / (12 * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hn0_nat : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn0_nat
  have hendpoint :=
    abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_unconditional
      F hF hn
  have htail : |negativeLaplaceTailError n| ≤ 4 / (n : ℝ) := by
    have hexp : (n : ℝ) ≤ Real.exp n := by
      exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
        (Real.add_one_le_exp n)
    have hinv : Real.exp (-(n : ℝ)) ≤ (n : ℝ)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hn0).2 hexp
    have hlogn : Real.log 2 ≤ (n : ℝ) := by
      have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith [Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 2) (by norm_num)]
    calc
      |negativeLaplaceTailError n| ≤ 4 * Real.exp (-(n : ℝ)) :=
        abs_negativeLaplaceTailError_le_four_exp n hlogn
      _ ≤ 4 * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 4 / (n : ℝ) := by rw [div_eq_mul_inv]
  have hstirling : |dyadicStirlingLogError n| ≤ 1 / (12 * (n : ℝ)) := by
    obtain ⟨hzero, hupper⟩ := dyadicStirlingLogError_bounds n hn1
    rw [abs_of_nonneg hzero]
    exact hupper
  have hidentity :
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
          dyadicSharpCumulantMain F n =
        negativeLaplaceTailError n +
          (dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n) -
            dyadicStirlingLogError n := by
    rw [log_fabius_dyadic_exact_sharp_decomposition_centered F hF n hn1]
    unfold dyadicSharpCumulantMain
    ring
  rw [hidentity]
  calc
    |negativeLaplaceTailError n +
        (dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n) -
          dyadicStirlingLogError n| ≤
      |negativeLaplaceTailError n| +
        |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| +
          |dyadicStirlingLogError n| := by
        calc
          _ ≤ |negativeLaplaceTailError n +
              (dyadicEndpointLaplaceLogError n +
                dyadicEndpointSecondOrder F n)| +
              |dyadicStirlingLogError n| := by
                simpa only [sub_eq_add_neg, abs_neg] using
                  (abs_add_le
                    (negativeLaplaceTailError n +
                      (dyadicEndpointLaplaceLogError n +
                        dyadicEndpointSecondOrder F n))
                    (-dyadicStirlingLogError n))
          _ ≤ (|negativeLaplaceTailError n| +
                |dyadicEndpointLaplaceLogError n +
                  dyadicEndpointSecondOrder F n|) +
              |dyadicStirlingLogError n| := by
                have h := abs_add_le (negativeLaplaceTailError n)
                  (dyadicEndpointLaplaceLogError n +
                    dyadicEndpointSecondOrder F n)
                linarith
    _ ≤ 4 / (n : ℝ) + 209408 / (n : ℝ) + 1 / (12 * (n : ℝ)) := by
      gcongr
    _ = 2512945 / (12 * (n : ℝ)) := by
      field_simp [hn0.ne']
      norm_num

/-- Asymptotic compatibility form of the effective sharp dyadic formula with
the exact cumulant correction. -/
theorem log_fabius_dyadic_sub_cumulantMain_isBigO_unconditional
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ =>
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpCumulantMain F n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply IsBigO.of_bound (2512945 / 12)
  filter_upwards [eventually_atTop.2 ⟨224043, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn0)]
  have h := abs_log_fabius_dyadic_sub_cumulantMain_le_unconditional F hF hn
  calc
    |Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpCumulantMain F n| ≤ 2512945 / (12 * (n : ℝ)) := h
    _ = (2512945 / 12) * (n : ℝ)⁻¹ := by field_simp

end Fabius
