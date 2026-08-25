import FabiusFunction.AnalyticMoments
import FabiusFunction.FourierAnalytic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The sinc product for the Fourier transform of Rvachev's function

This module proves the first equality in equation (5) of Arias de Reyna's
paper.  The removable complex sinc factors form a genuine convergent infinite
product, and the Fourier transform satisfies the corresponding finite
refinement identity.  Passing to the limit identifies the two functions.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter Set

namespace Fabius

noncomputable section

/-- The removable complex sinc is the divided slope of sine at zero. -/
lemma complexSinc_eq_dslope : complexSinc = dslope Complex.sin 0 := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  · rw [complexSinc, if_neg hz, dslope_of_ne _ hz, slope_def_field]
    simp

/-- The removable complex sinc is entire. -/
lemma complexSinc_differentiable : Differentiable ℂ complexSinc := by
  rw [complexSinc_eq_dslope]
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (s := Set.univ) (c := 0)
    (univ_mem : Set.univ ∈ nhds (0 : ℂ))).2
      Complex.differentiable_sin.differentiableOn

/-- Near zero, the deviation of complex sinc from one is at most linear. -/
lemma complexSinc_sub_one_isBigO :
    (fun z : ℂ => complexSinc z - 1) =O[nhds 0] (fun z : ℂ => z) := by
  have h := (complexSinc_differentiable.differentiableAt :
    DifferentiableAt ℂ complexSinc 0).isBigO_sub
  simpa [complexSinc] using h

/-- The half-angle factorization of the removable complex sinc function,
`sinc z = cos (z / 2) * sinc (z / 2)`.

The strictly upstream home for this fact (and for `complexSinc_neg` below)
would be `FabiusFunction.Basic`, where `complexSinc` itself is defined; it is
placed here instead because `Basic` sits at the root of the import graph and
editing it invalidates every module in the development.  This module is the
earliest one already imported by all three former duplication sites
(`WeakConvergence`, `PoissonSummation`, `OriginalPaperSupplement`), so no
import path changes. -/
theorem complexSinc_eq_cos_mul (z : ℂ) :
    complexSinc z = Complex.cos (z / 2) * complexSinc (z / 2) := by
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  · have hz2 : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
    rw [complexSinc, if_neg hz, complexSinc, if_neg hz2]
    have htwo : 2 * (z / 2) = z := by ring
    rw [← htwo, Complex.sin_two_mul]
    field_simp

/-- The removable complex sinc function is even. -/
theorem complexSinc_neg (z : ℂ) : complexSinc (-z) = complexSinc z := by
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  · simp only [complexSinc, neg_eq_zero, hz, if_false, Complex.sin_neg]
    field_simp

/-- The dyadically scaled Fourier arguments form a summable complex series. -/
lemma dyadicComplex_summable (z : ℂ) :
    Summable (fun n : ℕ => (Real.pi : ℂ) * z / (2 : ℂ) ^ n) := by
  have hgeom : Summable (fun n : ℕ => ((2 : ℂ)⁻¹) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  have hmul := hgeom.mul_left ((Real.pi : ℂ) * z)
  apply hmul.congr
  intro n
  rw [inv_pow]
  ring

/-- The sinc factors in Rvachev's Fourier product are genuinely multipliable. -/
lemma sincFactors_multipliable (z : ℂ) :
    Multipliable (fun n : ℕ => complexSinc (Real.pi * z / (2 : ℂ) ^ n)) := by
  have hsum : Summable (fun n : ℕ =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) - 1) := by
    exact complexSinc_sub_one_isBigO.comp_summable (dyadicComplex_summable z)
  have hp := Complex.multipliable_one_add_of_summable hsum
  convert hp using 1
  funext n
  ring

/-- Rvachev's Fourier transform is normalized to one at the origin. -/
@[simp] theorem rvachevFourier_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    rvachevFourier F 0 = 1 := by
  have h := complexGeneratingFunction_eq_fourier_analytic F hF 0
  simpa [complexGeneratingFunction] using h.symm

/-- The Fourier refinement identity used explicitly in the proof of
Proposition 2 of *Arithmetic of the Fabius function*. -/
theorem rvachevFourier_scaling
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevFourier F z =
      complexSinc (Real.pi * z) * rvachevFourier F (z / 2) := by
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  let q : ℂ := -2 * Real.pi * Complex.I * z
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) hz
  have harg_two : Complex.I * (2 * q) / (4 * Real.pi) = z := by
    dsimp [q]
    field_simp [hpi]
    rw [Complex.I_sq]
    ring
  have harg_one : Complex.I * q / (4 * Real.pi) = z / 2 := by
    dsimp [q]
    field_simp [hpi]
    rw [Complex.I_sq]
    ring
  have hprop := proposition_two_formula F hF q
  rw [complexGeneratingFunction_eq_fourier_analytic F hF (2 * q),
    complexGeneratingFunction_eq_fourier_analytic F hF q,
    harg_two, harg_one, complexExpm1Div_of_ne hq] at hprop
  have htwo : 2 * q / 2 = q := by ring
  rw [htwo] at hprop
  have hcoef :
      Complex.exp (-q) * ((Complex.exp q - 1) / q * Complex.exp (q / 2)) =
        complexSinc (Real.pi * z) := by
    rw [complexSinc, if_neg (mul_ne_zero hpi hz), Complex.sin]
    dsimp [q]
    field_simp [hpi, hz, Complex.I_ne_zero]
    have hcancel :
        Complex.exp (2 * Real.pi * Complex.I * z) *
            Complex.exp (-(2 * Real.pi * Complex.I * z)) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hhalf :
        Complex.exp (2 * Real.pi * Complex.I * z) *
            Complex.exp (-(Real.pi * Complex.I * z)) =
          Complex.exp (Real.pi * Complex.I * z) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [Complex.I_sq, neg_one_mul]
    calc
      -(Complex.exp (2 * Real.pi * Complex.I * z) *
          (Complex.exp (-(2 * Real.pi * Complex.I * z)) - 1) *
            Complex.exp (-(Real.pi * Complex.I * z))) =
          -((Complex.exp (2 * Real.pi * Complex.I * z) *
              Complex.exp (-(2 * Real.pi * Complex.I * z))) *
                Complex.exp (-(Real.pi * Complex.I * z)) -
            Complex.exp (2 * Real.pi * Complex.I * z) *
              Complex.exp (-(Real.pi * Complex.I * z))) := by ring
      _ = -(Complex.exp (-(Real.pi * Complex.I * z)) -
          Complex.exp (Real.pi * Complex.I * z)) := by rw [hcancel, hhalf, one_mul]
  calc
    rvachevFourier F z =
        Complex.exp (-q) * (Complex.exp q * rvachevFourier F z) := by
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = Complex.exp (-q) *
        (((Complex.exp q - 1) / q) *
          (Complex.exp (q / 2) * rvachevFourier F (z / 2))) := by
      rw [hprop]
    _ = complexSinc (Real.pi * z) * rvachevFourier F (z / 2) := by
      rw [← hcoef]
      ring

/-- The refinement identity iterated through any finite number of sinc factors. -/
theorem rvachevFourier_eq_finite_product
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) (N : ℕ) :
    rvachevFourier F z =
      (∏ n ∈ Finset.range N,
        complexSinc (Real.pi * z / (2 : ℂ) ^ n)) *
          rvachevFourier F (z / (2 : ℂ) ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        rvachevFourier F z =
            (∏ n ∈ Finset.range N,
              complexSinc (Real.pi * z / (2 : ℂ) ^ n)) *
                rvachevFourier F (z / (2 : ℂ) ^ N) := ih
        _ = (∏ n ∈ Finset.range N,
              complexSinc (Real.pi * z / (2 : ℂ) ^ n)) *
                (complexSinc (Real.pi * (z / (2 : ℂ) ^ N)) *
                  rvachevFourier F ((z / (2 : ℂ) ^ N) / 2)) := by
            rw [rvachevFourier_scaling F hF]
        _ = (∏ n ∈ Finset.range (N + 1),
              complexSinc (Real.pi * z / (2 : ℂ) ^ n)) *
                rvachevFourier F (z / (2 : ℂ) ^ (N + 1)) := by
            rw [Finset.prod_range_succ]
            have hf : complexSinc (Real.pi * (z / (2 : ℂ) ^ N)) =
                complexSinc (Real.pi * z / (2 : ℂ) ^ N) := by
              congr 1
              ring
            have ht : (z / (2 : ℂ) ^ N) / 2 =
                z / (2 : ℂ) ^ (N + 1) := by
              rw [pow_succ]
              ring
            rw [hf, ht]
            ring

/-- Equation (5): Rvachev's Fourier transform is its infinite sinc product. -/
theorem rvachevFourier_eq_product
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevFourier F z = rvachevFourierProduct z := by
  have hargs : Tendsto (fun N : ℕ => z / (2 : ℂ) ^ N) atTop (nhds 0) := by
    have hpow : Tendsto (fun N : ℕ => ((2 : ℂ)⁻¹) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    simpa [div_eq_mul_inv] using hpow.const_mul z
  have htail0 : Tendsto
      (fun N : ℕ => rvachevFourier F (z / (2 : ℂ) ^ N)) atTop
        (nhds (rvachevFourier F 0)) := by
    have hcont : Tendsto (rvachevFourier F) (nhds 0)
        (nhds (rvachevFourier F 0)) :=
      (rvachevFourier_differentiable_analytic F hF).continuous.continuousAt
    exact hcont.comp hargs
  have htail : Tendsto
      (fun N : ℕ => rvachevFourier F (z / (2 : ℂ) ^ N)) atTop
        (nhds 1) := by
    simpa [rvachevFourier_zero F hF] using htail0
  have hmult : Multipliable fun n : ℕ =>
      complexSinc (Real.pi * z / (2 : ℂ) ^ n) :=
    sincFactors_multipliable z
  have hprod : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N,
        complexSinc (Real.pi * z / (2 : ℂ) ^ n)) atTop
      (nhds (∏' n : ℕ, complexSinc (Real.pi * z / (2 : ℂ) ^ n))) :=
    hmult.tendsto_prod_tprod_nat
  have hmul := hprod.mul htail
  have hlim : Tendsto (fun _N : ℕ => rvachevFourier F z) atTop
      (nhds (∏' n : ℕ, complexSinc (Real.pi * z / (2 : ℂ) ^ n))) := by
    simpa only [mul_one] using hmul.congr'
      (Filter.Eventually.of_forall fun N =>
        (rvachevFourier_eq_finite_product F hF z N).symm)
  unfold rvachevFourierProduct
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end


end Fabius
