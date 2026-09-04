import FabiusFunction.FabiusLegendreTranslateBlocks

/-!
# Finite Legendre--Rvachev biorthogonality

Exact polynomial synthesis by shifted copies of Rvachev's `up` function has
a finite dual formulation.  Pairing the degree-`l` synthesis identity with
the normalized degree-`m` Legendre polynomial produces the Kronecker delta.
The resulting analysis kernel is

`(2 * m + 1) / 2 * ∫ x in -1..1, up (x - c) * P_m(x)`.

This module records precisely that finite biorthogonality statement.  It does
not assert the stronger finite-matrix projector identities, reverse spectral
closure, or any rationality formula for the analysis kernel.
-/

set_option autoImplicit false

open MeasureTheory Polynomial Set Finset
open scoped BigOperators Interval

namespace Fabius

noncomputable section

/-- The normalized Legendre analysis coefficient of the Rvachev atom centered
at `c`.  The factor `(2m+1)/2` is the reciprocal squared norm of the ordinary
degree-`m` Legendre polynomial on `[-1,1]`. -/
noncomputable def rvachevLegendreAnalysisKernel
    (F : BoundedFabius) (m : ℕ) (c : ℝ) : ℝ :=
  (((2 * m + 1 : ℕ) : ℝ) / 2) *
    ∫ x in (-1 : ℝ)..1,
      rvachevUp F (x - c) * (legendrePolynomial m).eval x

/-- **Finite Legendre--Rvachev biorthogonality.**  If the natural mesh `M`
has two-adic valuation at least `l`, then the normalized samples of the
degree-`l` Rvachev deconvolution polynomial are biorthogonal to the Legendre
analysis kernels.  The open integer block is exactly the manuscript's
`|k| < 2M`, and `M ≠ 0` is its positive-mesh hypothesis. -/
theorem rvachevLegendreBiorthogonality
    (F : BoundedFabius) (hF : IsFabius F)
    {M : ℕ} (hM : M ≠ 0) (l m : ℕ)
    (hl : l ≤ padicValNat 2 M) :
    ((M : ℝ))⁻¹ *
        ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
          (rvachevLegendreDeconvolutionPolynomial l).eval
              ((k : ℝ) / (M : ℝ)) *
            rvachevLegendreAnalysisKernel F m ((k : ℝ) / (M : ℝ)) =
      if m = l then 1 else 0 := by
  let c : ℝ := ((2 * m + 1 : ℕ) : ℝ) / 2
  let q : ℤ → ℝ := fun k ↦
    (rvachevLegendreDeconvolutionPolynomial l).eval
      ((k : ℝ) / (M : ℝ))
  let u : ℤ → ℝ → ℝ := fun k x ↦
    rvachevUp F (x - (k : ℝ) / (M : ℝ))
  let p : ℝ → ℝ := fun x ↦ (legendrePolynomial m).eval x
  have hsynth (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      ((M : ℝ))⁻¹ *
          ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
            q k * u k x =
        (legendrePolynomial l).eval x := by
    exact
      normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
        F hF hM (P := legendrePolynomial l)
          (by simpa only [natDegree_legendrePolynomial] using hl) hx
  have hterm (k : ℤ) :
      IntervalIntegrable
        (fun x : ℝ ↦
          (((M : ℝ))⁻¹ * q k) * (u k x * p x))
        volume (-1 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (((rvachev_contDiff F hF).continuous.comp
          (continuous_id.sub continuous_const)).mul
        (legendrePolynomial_contDiff m).continuous)
  have hswap :
      (∫ x in (-1 : ℝ)..1,
          ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
            (((M : ℝ))⁻¹ * q k) * (u k x * p x)) =
        ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
          ∫ x in (-1 : ℝ)..1,
            (((M : ℝ))⁻¹ * q k) * (u k x * p x) := by
    rw [intervalIntegral.integral_finsetSum (fun k _hk ↦ hterm k)]
  change ((M : ℝ))⁻¹ *
      ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
        q k * (c * ∫ x in (-1 : ℝ)..1, u k x * p x) = _
  calc
    ((M : ℝ))⁻¹ *
          ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
            q k * (c * ∫ x in (-1 : ℝ)..1, u k x * p x) =
        c *
          ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
            ∫ x in (-1 : ℝ)..1,
              (((M : ℝ))⁻¹ * q k) * (u k x * p x) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = c *
        ∫ x in (-1 : ℝ)..1,
          ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
            (((M : ℝ))⁻¹ * q k) * (u k x * p x) := by
      rw [hswap]
    _ = c *
        ∫ x in (-1 : ℝ)..1,
          (((M : ℝ))⁻¹ *
              ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
                q k * u k x) * p x := by
      apply congrArg (fun z : ℝ ↦ c * z)
      apply intervalIntegral.integral_congr
      intro x _hx
      calc
        (∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
            (((M : ℝ))⁻¹ * q k) * (u k x * p x)) =
            ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
              ((M : ℝ))⁻¹ * ((q k * u k x) * p x) := by
          apply Finset.sum_congr rfl
          intro k _hk
          ring
        _ = ((M : ℝ))⁻¹ *
            ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
              (q k * u k x) * p x := by
          rw [Finset.mul_sum]
        _ = (((M : ℝ))⁻¹ *
              ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
                q k * u k x) * p x := by
          rw [← Finset.sum_mul]
          ring
    _ = c *
        ∫ x in (-1 : ℝ)..1,
          (legendrePolynomial l).eval x * p x := by
      apply congrArg (fun z : ℝ ↦ c * z)
      apply intervalIntegral.integral_congr
      intro x hx
      have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      simpa only using
        congrArg (fun z : ℝ ↦ z * p x) (hsynth x hxIcc)
    _ = if m = l then 1 else 0 := by
      rw [integral_eval_legendrePolynomial_mul]
      by_cases hml : m = l
      · subst l
        simp only [if_pos]
        dsimp only [c]
        have hden : (((2 * m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      · have hlm : l ≠ m := Ne.symm hml
        simp only [if_neg hml, if_neg hlm, mul_zero]

end

end Fabius
