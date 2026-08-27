import FabiusFunction.LogProductMoments
import FabiusFunction.LacunaryRieszIntegral

/-!
# The `2^{-n/2}` orthogonality bound for lacunary `L¹` means

`SincMeanBracket` bounds the mean of the lacunary sine product by
`(√3/2)ⁿ ≈ 0.866ⁿ`, inherited from the pointwise Gelfond bound.  The
`L²` route gives a strict quantitative improvement: Cauchy–Schwarz on the
unit interval against the *exact* second moment

`∫₀¹ ∏_{j<n} sin²(πbʲt) dt = 2⁻ⁿ`  (`integral_prod_sin_sq_pow`)

gives the same bound for every positive integer frequency sequence satisfying
the Hadamard gap condition `2 mⱼ ≤ mⱼ₊₁`; in particular, for every
integer base `b ≥ 2`,

`I₁(b,n) = ∫₀¹ ∏_{j<n} |sin(πbʲt)| dt ≤ 2^{-n/2} = (√2/2)ⁿ ≈ 0.7071ⁿ`.

The Cauchy–Schwarz step is `sq_integral_abs_le` from
`LogProductMoments`, proved there by expanding `∫(|f| − c)² ≥ 0`, so
no `L²`-space machinery is involved anywhere in this file.

* `integral_prod_abs_sin_le_sqrt_two` — **the general orthogonality bound**
  for gap-`2` integer frequencies.
* `integral_prod_abs_sin_pow_le_sqrt_two` — its specialization to every
  integer base `b ≥ 2`.
* `integral_prod_abs_sin_two_pow_le_sqrt_two` — its dyadic specialization.
* `integral_prod_abs_sin_two_pow_le_sqrt_two'` — in the `range (n+1)`
  indexing of `SincMeanBracket`, for direct comparison.
-/

set_option autoImplicit false

open Finset Real MeasureTheory

namespace Fabius

/-- **The lacunary `L¹` orthogonality bound**: if the positive integer
frequencies satisfy `2 mⱼ ≤ mⱼ₊₁`, then
`∫₀¹ ∏_{j<n} |sin(π mⱼ t)| dt ≤ (√2/2)ⁿ`.

The constant is independent of the frequencies: the gap condition makes
all nonconstant Fourier modes in the squared product orthogonal, leaving the
same exact second moment `2⁻ⁿ`; Cauchy–Schwarz then gives the stated
bound. -/
theorem integral_prod_abs_sin_le_sqrt_two (n : ℕ) (m : ℕ → ℕ)
    (hgap : ∀ j, 2 * m j ≤ m (j + 1)) (hpos : 0 < m 0) :
    ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * (m j : ℝ) * t)| ≤
      (Real.sqrt 2 / 2) ^ n := by
  set f : ℝ → ℝ := fun t => ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t)
    with hf
  have hcont : Continuous f := by
    rw [hf]
    exact continuous_finsetProd _ (fun j _ => by fun_prop)
  have hint : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable _ _
  have hintsq : IntervalIntegrable (fun t => f t ^ 2)
      MeasureTheory.volume 0 1 :=
    (hcont.pow 2).intervalIntegrable _ _
  -- Cauchy–Schwarz against the exact second moment
  have hCS := sq_integral_abs_le hint hintsq
  have habs : (∫ t in (0:ℝ)..1, |f t|) =
      ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * (m j : ℝ) * t)| := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hf]
    exact Finset.abs_prod _ _
  have hsq : (∫ t in (0:ℝ)..1, f t ^ 2) = (1 / 2 : ℝ) ^ n := by
    have hpt : ∀ t : ℝ, f t ^ 2 =
        ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2 := by
      intro t
      rw [hf]
      exact (Finset.prod_pow _ _ _).symm
    rw [intervalIntegral.integral_congr (g := fun t =>
      ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2)
      (fun t _ => hpt t)]
    exact integral_prod_sin_sq n m hgap hpos
  rw [habs, hsq] at hCS
  -- take square roots
  have hI0 : 0 ≤ ∫ t in (0:ℝ)..1,
      ∏ j ∈ range n, |Real.sin (π * (m j : ℝ) * t)| :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun u _ => Finset.prod_nonneg (fun j _ => abs_nonneg _))
  have hroot := Real.sqrt_le_sqrt hCS
  rw [Real.sqrt_sq hI0] at hroot
  have hval : Real.sqrt ((1/2 : ℝ) ^ n) = (Real.sqrt 2 / 2) ^ n := by
    have hnn : (0:ℝ) ≤ (Real.sqrt 2 / 2) ^ n := by positivity
    have hsq : ((Real.sqrt 2 / 2) ^ n) ^ 2 = (1/2 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, div_pow,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [← hsq, Real.sqrt_sq hnn]
  rwa [hval] at hroot

/-- For geometric integer frequencies `bʲ` with `b ≥ 2`, the general
orthogonality bound reads
`∫₀¹ ∏_{j<n} |sin(π bʲ t)| dt ≤ (√2/2)ⁿ`. -/
theorem integral_prod_abs_sin_pow_le_sqrt_two (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * (b : ℝ) ^ j * t)| ≤
      (Real.sqrt 2 / 2) ^ n := by
  have h := integral_prod_abs_sin_le_sqrt_two n (fun j => b ^ j)
    (fun j => by
      have : 2 * b ^ j ≤ b * b ^ j := Nat.mul_le_mul_right _ hb
      simpa [pow_succ, mul_comm] using this)
    (by simp)
  have hcast : ∀ (j : ℕ) (t : ℝ),
      Real.sin (π * ((b ^ j : ℕ) : ℝ) * t) =
        Real.sin (π * (b : ℝ) ^ j * t) := by
    intro j t
    norm_num
  simpa [hcast] using h

/-- **The dyadic `L¹` orthogonality bound**:
`∫₀¹ ∏_{j<n} |sin(π2ʲt)| dt ≤ (√2/2)ⁿ`. -/
theorem integral_prod_abs_sin_two_pow_le_sqrt_two (n : ℕ) :
    ∫ t in (0:ℝ)..1, ∏ j ∈ range n, |Real.sin (π * 2 ^ j * t)| ≤
      (Real.sqrt 2 / 2) ^ n := by
  simpa using integral_prod_abs_sin_pow_le_sqrt_two 2 le_rfl n

/-- The same bound in the `range (n+1)` indexing of
`integral_prod_abs_sin_two_pow_le`, exhibiting it as a sharpening of
that `(√3/2)ⁿ` bracket. -/
theorem integral_prod_abs_sin_two_pow_le_sqrt_two' (n : ℕ) :
    ∫ t in (0:ℝ)..1, ∏ j ∈ range (n + 1), |Real.sin (π * 2 ^ j * t)| ≤
      (Real.sqrt 2 / 2) ^ (n + 1) :=
  integral_prod_abs_sin_two_pow_le_sqrt_two (n + 1)

end Fabius
