import FabiusFunction.RvachevMomentAppell
import FabiusFunction.CompositeMeshExactness

/-!
# Exact polynomial synthesis by shifted Rvachev atoms

This module combines two finite-degree mechanisms:

* `rvachevDeconvolvedPolynomial` inverts smoothing by the normalized Rvachev
  density on real polynomials;
* `tsum_shifted_polynomial_eq_integral_nat` replaces a scaled Rvachev
  integral by its integer comb whenever the polynomial degree is at most the
  two-adic valuation of the mesh.

After an affine change of variables, their composition gives the literal
shift synthesis formula

`sum_k D(P)(k / M) * up(x - k / M) = M * P(x)`.

Thus division by `M` reconstructs `P` from samples of its Rvachev
deconvolution on the lattice of spacing `1 / M`.  The infinite sum is in fact
pointwise finite.  On `[-1, 1]`, support of `up` truncates it uniformly to the
exact integer interval `(-2M, 2M)`; the two excluded boundary atoms vanish at
the support endpoints.
-/

set_option autoImplicit false

open MeasureTheory Polynomial Set
open scoped BigOperators

namespace Fabius

/-- **Global Rvachev polynomial synthesis.**  Let `M` be a nonzero natural
mesh and let `P` have degree at most `v₂(M)`.  Sampling the Rvachev
deconvolution of `P` on the lattice `k / M` and attaching the unscaled atom
`up(x - k / M)` reconstructs `M * P(x)` for every real `x`.

The `tsum` is pointwise finite because `rvachevUp` has compact support. -/
theorem tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {P : ℝ[X]} (hdeg : P.natDegree ≤ padicValNat 2 M) (x : ℝ) :
    ∑' k : ℤ,
        (rvachevDeconvolvedPolynomial P).eval ((k : ℝ) / (M : ℝ)) *
          rvachevUp F (x - (k : ℝ) / (M : ℝ)) =
      (M : ℝ) * P.eval x := by
  let Q : ℝ[X] := rvachevDeconvolvedPolynomial P
  let R : ℝ[X] :=
    Q.comp (C ((M : ℝ)⁻¹) * X + C x)
  have hRdeg : R.natDegree ≤ padicValNat 2 M := by
    calc
      R.natDegree ≤
          Q.natDegree * (C ((M : ℝ)⁻¹) * X + C x).natDegree := by
        exact Polynomial.natDegree_comp_le
      _ ≤ Q.natDegree * 1 := by
        exact Nat.mul_le_mul_left Q.natDegree Polynomial.natDegree_linear_le
      _ = Q.natDegree := by omega
      _ ≤ P.natDegree := by
        exact natDegree_rvachevDeconvolvedPolynomial_le P
      _ ≤ padicValNat 2 M := hdeg
  have hcomb := tsum_shifted_polynomial_eq_integral_nat F hF hM hRdeg
    (-(M : ℝ) * x)
  have hMreal : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hsummand : ∀ k : ℤ,
      R.eval (-(M : ℝ) * x + (k : ℝ)) *
          rvachevUp F
            (((M : ℝ))⁻¹ * (-(M : ℝ) * x + (k : ℝ))) =
        Q.eval ((k : ℝ) / (M : ℝ)) *
          rvachevUp F (x - (k : ℝ) / (M : ℝ)) := by
    intro k
    have hscaled :
        ((M : ℝ))⁻¹ * (-(M : ℝ) * x + (k : ℝ)) =
          (k : ℝ) / (M : ℝ) - x := by
      field_simp [hMreal]
      ring
    simp only [R, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [hscaled]
    have hsample : (k : ℝ) / (M : ℝ) - x + x =
        (k : ℝ) / (M : ℝ) := by ring
    rw [hsample]
    have hneg : (k : ℝ) / (M : ℝ) - x =
        -(x - (k : ℝ) / (M : ℝ)) := by ring
    rw [hneg, rvachevUp_even F]
  have hintegral :
      (∫ z : ℝ, R.eval z * rvachevUp F (((M : ℝ))⁻¹ * z)) =
        (M : ℝ) * P.eval x := by
    have hscale := MeasureTheory.Measure.integral_comp_inv_mul_left
      (fun y : ℝ ↦ Q.eval (x + y) * rvachevUp F y) (M : ℝ)
    have hsmooth :
        (∫ y : ℝ, Q.eval (x + y) * rvachevUp F y) = P.eval x := by
      simpa only [Q] using
        integral_eval_rvachevDeconvolvedPolynomial_add_mul_rvachev
          F hF P x
    calc
      (∫ z : ℝ, R.eval z * rvachevUp F (((M : ℝ))⁻¹ * z)) =
          ∫ z : ℝ,
            Q.eval (x + ((M : ℝ))⁻¹ * z) *
              rvachevUp F (((M : ℝ))⁻¹ * z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
        simp only [R, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        congr 2
        ring
      _ = (M : ℝ) *
          ∫ y : ℝ, Q.eval (x + y) * rvachevUp F y := by
        simpa only [abs_of_nonneg
          (show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M), smul_eq_mul] using
          hscale
      _ = (M : ℝ) * P.eval x := by rw [hsmooth]
  calc
    (∑' k : ℤ,
        (rvachevDeconvolvedPolynomial P).eval ((k : ℝ) / (M : ℝ)) *
          rvachevUp F (x - (k : ℝ) / (M : ℝ))) =
        ∑' k : ℤ,
          R.eval (-(M : ℝ) * x + (k : ℝ)) *
            rvachevUp F
              (((M : ℝ))⁻¹ * (-(M : ℝ) * x + (k : ℝ))) := by
      exact tsum_congr fun k ↦ (hsummand k).symm
    _ = ∫ z : ℝ, R.eval z * rvachevUp F (((M : ℝ))⁻¹ * z) := hcomb
    _ = (M : ℝ) * P.eval x := hintegral

/-- Normalized global synthesis: after multiplying by the lattice spacing
`1 / M`, the shifted Rvachev atom sum equals `P(x)` exactly. -/
theorem normalized_tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {P : ℝ[X]} (hdeg : P.natDegree ≤ padicValNat 2 M) (x : ℝ) :
    ((M : ℝ))⁻¹ *
        ∑' k : ℤ,
          (rvachevDeconvolvedPolynomial P).eval ((k : ℝ) / (M : ℝ)) *
            rvachevUp F (x - (k : ℝ) / (M : ℝ)) =
      P.eval x := by
  rw [tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
    F hF hM hdeg x]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hM), one_mul]

/-- **Uniform finite synthesis on `[-1,1]`.**  In the global reconstruction
formula, every atom outside the exact integer interval `(-2M, 2M)` vanishes
on `[-1,1]`.  The boundary indices `±2M` vanish as well, so the open
interval contains precisely every potentially contributing index. -/
theorem sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {P : ℝ[X]} (hdeg : P.natDegree ≤ padicValNat 2 M)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
        (rvachevDeconvolvedPolynomial P).eval ((k : ℝ) / (M : ℝ)) *
          rvachevUp F (x - (k : ℝ) / (M : ℝ)) =
      (M : ℝ) * P.eval x := by
  have hMpos : (0 : ℝ) < (M : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  calc
    (∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
        (rvachevDeconvolvedPolynomial P).eval ((k : ℝ) / (M : ℝ)) *
          rvachevUp F (x - (k : ℝ) / (M : ℝ))) =
        ∑' k : ℤ,
          (rvachevDeconvolvedPolynomial P).eval ((k : ℝ) / (M : ℝ)) *
            rvachevUp F (x - (k : ℝ) / (M : ℝ)) := by
      symm
      apply tsum_eq_sum
      intro k hk
      simp only [Finset.mem_Ioo, not_and_or, not_lt] at hk
      rcases hk with hk | hk
      · have hkreal : (k : ℝ) ≤ -(2 * (M : ℝ)) := by
          exact_mod_cast hk
        have hquot : (k : ℝ) / (M : ℝ) ≤ -2 := by
          apply (div_le_iff₀ hMpos).2
          nlinarith
        rw [rvachevUp_eq_zero_of_one_le F hF (by linarith [hx.1]), mul_zero]
      · have hkreal : 2 * (M : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast hk
        have hquot : 2 ≤ (k : ℝ) / (M : ℝ) := by
          apply (le_div_iff₀ hMpos).2
          nlinarith
        rw [rvachevUp_eq_zero_of_le_neg_one F hF (by linarith [hx.2]), mul_zero]
    _ = (M : ℝ) * P.eval x :=
      tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
        F hF hM hdeg x

/-- Normalized finite synthesis on `[-1,1]`: the open integer block
`(-2M, 2M)` reconstructs `P(x)` after multiplication by `1 / M`. -/
theorem normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0)
    {P : ℝ[X]} (hdeg : P.natDegree ≤ padicValNat 2 M)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ((M : ℝ))⁻¹ *
        ∑ k ∈ Finset.Ioo (-(2 * (M : ℤ))) (2 * (M : ℤ)),
          (rvachevDeconvolvedPolynomial P).eval ((k : ℝ) / (M : ℝ)) *
            rvachevUp F (x - (k : ℝ) / (M : ℝ)) =
      P.eval x := by
  rw [sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp
    F hF hM hdeg hx]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hM), one_mul]

end Fabius
