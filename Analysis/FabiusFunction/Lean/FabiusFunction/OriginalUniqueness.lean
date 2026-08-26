import FabiusFunction.OriginalCharacterization
import FabiusFunction.Existence
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion

/-!
# Uniqueness in the original Rvachev characterization

This file proves the uniqueness half of Theorem 1 of arXiv:1702.05442 by
the Fourier-refinement argument used in the paper.  The intermediate Fourier
facts are part of the public API: every original solution has transform value
one at the origin, satisfies the finite and infinite dyadic sinc-product
formulas, and consequently has the same transform as every other solution.
The final equivalences identify these original solutions with the scale-two
folds of unique bounded `IsFabius` witnesses, describe exactly which values a
fold forgets, and recover a sharp fixed-candidate characterization by restoring
the omitted right tail.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Filter MeasureTheory Set

namespace Fabius

noncomputable section

namespace IsOriginalFabius

variable {φ : ℝ → ℝ} {k : ℝ} (h : IsOriginalFabius φ k)

include h

/-- The real-to-complex coercion of an original solution. -/
private abbrev complexFunction (φ : ℝ → ℝ) : ℝ → ℂ := fun x => (φ x : ℂ)

private theorem complex_hasCompactSupport :
    HasCompactSupport (complexFunction φ) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hmem
  have hz := h.eq_zero_of_not_mem hmem
  exact hx (by simp [complexFunction, hz])

private theorem complex_contDiff : ContDiff ℝ ∞ (complexFunction φ) := by
  change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ)
  exact Complex.ofRealCLM.contDiff.comp h.contDiff

private theorem complex_integrable : Integrable (complexFunction φ) :=
  (Complex.continuous_ofReal.comp h.contDiff.continuous).integrable_of_hasCompactSupport
    h.complex_hasCompactSupport

/-- The Fourier transform used in the uniqueness proof of the original paper. -/
noncomputable def originalFourier (φ : ℝ → ℝ) (z : ℝ) : ℂ :=
  𝓕 (complexFunction φ) z

/-- The Fourier transform of an original solution is continuous. -/
theorem originalFourier_continuous : Continuous (originalFourier φ) := by
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ h.complex_integrable

/-- Normalization of an original solution gives Fourier-transform value one at
frequency zero. -/
theorem originalFourier_zero : originalFourier φ 0 = 1 := by
  rw [originalFourier, Real.fourier_real_eq_integral_exp_smul]
  have hcast : (∫ x : ℝ, (φ x : ℂ)) =
      Complex.ofReal (∫ x : ℝ, φ x) := by
    exact integral_ofReal (𝕜 := ℂ)
  simp [hcast, h.integral_eq_one]

omit h in
private theorem affine_fourier (d z : ℝ) :
    𝓕 (fun x : ℝ => complexFunction φ (2 * x + d)) z =
      (1 / 2 : ℂ) * Complex.exp (Real.pi * Complex.I * d * z) *
        originalFourier φ (z / 2) := by
  let g : ℝ → ℂ := fun u =>
    Complex.exp (((-2 * Real.pi * u * (z / 2) : ℝ) : ℂ) * Complex.I) *
      complexFunction φ u
  have hshift : (∫ x : ℝ, g (2 * x + d)) = ∫ x : ℝ, g (2 * x) := by
    have ht : (∫ x : ℝ, g (2 * (x + d / 2))) = ∫ x : ℝ, g (2 * x) :=
      integral_add_right_eq_self (fun x : ℝ => g (2 * x)) (d / 2)
    convert ht using 1
    · apply integral_congr_ae
      filter_upwards with x
      congr 1
      ring
  have hscale : (∫ x : ℝ, g (2 * x)) = (1 / 2 : ℂ) * ∫ u : ℝ, g u := by
    have hs := MeasureTheory.Measure.integral_comp_mul_left g (2 : ℝ)
    convert hs using 1
    all_goals norm_num
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ,
      Complex.exp (((-2 * Real.pi * x * z : ℝ) : ℂ) * Complex.I) *
        complexFunction φ (2 * x + d)) = _
  have hphase : ∀ x : ℝ,
      Complex.exp (((-2 * Real.pi * x * z : ℝ) : ℂ) * Complex.I) *
          complexFunction φ (2 * x + d) =
        Complex.exp (Real.pi * Complex.I * d * z) * g (2 * x + d) := by
    intro x
    dsimp [g]
    have hexp :
        Complex.exp (((-2 * Real.pi * x * z : ℝ) : ℂ) * Complex.I) =
          Complex.exp (Real.pi * Complex.I * d * z) *
            Complex.exp (((-2 * Real.pi * (2 * x + d) * (z / 2) : ℝ) : ℂ) *
              Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [show (∫ x : ℝ,
      Complex.exp (((-2 * Real.pi * x * z : ℝ) : ℂ) * Complex.I) *
        complexFunction φ (2 * x + d)) =
      ∫ x : ℝ, Complex.exp (Real.pi * Complex.I * d * z) * g (2 * x + d) by
        apply integral_congr_ae
        filter_upwards with x
        exact hphase x]
  rw [integral_const_mul, hshift, hscale]
  unfold originalFourier
  rw [Real.fourier_real_eq_integral_exp_smul]
  change _ = _ * _ * (∫ u : ℝ,
    Complex.exp (((-2 * Real.pi * u * (z / 2) : ℝ) : ℂ) * Complex.I) *
      complexFunction φ u)
  dsimp [g]
  ring

private theorem affine_integrable (d : ℝ) :
    Integrable (fun x : ℝ => complexFunction φ (2 * x + d)) := by
  have hs : Integrable (fun x : ℝ => complexFunction φ (2 * x)) :=
    h.complex_integrable.comp_mul_left' (by norm_num)
  have ht := hs.comp_add_right (d / 2)
  convert ht using 1
  funext x
  congr 1
  ring

private theorem complex_hasDerivAt (x : ℝ) :
    HasDerivAt (complexFunction φ)
      ((k : ℂ) * (complexFunction φ (2 * x + 1) -
        complexFunction φ (2 * x - 1))) x := by
  convert (h.hasDerivAt x).ofReal_comp using 1
  all_goals
    push_cast
    ring

private theorem complex_deriv :
    deriv (complexFunction φ) = fun x : ℝ =>
      (k : ℂ) * (complexFunction φ (2 * x + 1) -
        complexFunction φ (2 * x - 1)) := by
  funext x
  exact (h.complex_hasDerivAt x).deriv

/-- The Fourier transform of every solution of the original characterization
satisfies the dyadic sinc refinement equation. -/
theorem originalFourier_scaling (z : ℝ) :
    originalFourier φ z =
      complexSinc (Real.pi * (z : ℂ)) * originalFourier φ (z / 2) := by
  have hdiff : Differentiable ℝ (complexFunction φ) :=
    h.complex_contDiff.differentiable (by simp)
  have hderivInt : Integrable (deriv (complexFunction φ)) :=
    (h.complex_contDiff.continuous_deriv (by simp)).integrable_of_hasCompactSupport
      h.complex_hasCompactSupport.deriv
  have hfourier := congrFun
    (Real.fourier_deriv h.complex_integrable hdiff hderivInt) z
  have hleft : 𝓕 (deriv (complexFunction φ)) z =
      (k : ℂ) *
        (𝓕 (fun x : ℝ => complexFunction φ (2 * x + 1)) z -
          𝓕 (fun x : ℝ => complexFunction φ (2 * x - 1)) z) := by
    rw [h.complex_deriv, Real.fourier_real_eq_integral_exp_smul]
    let e : ℝ → ℂ := fun x =>
      Complex.exp (((-2 * Real.pi * x * z : ℝ) : ℂ) * Complex.I)
    have he_meas : AEStronglyMeasurable e :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have he_bound : ∀ᵐ x : ℝ, ‖e x‖ ≤ (1 : ℝ) := by
      filter_upwards with x
      dsimp [e]
      rw [Complex.norm_exp]
      norm_num
    have hplus : Integrable (fun x : ℝ => e x * complexFunction φ (2 * x + 1)) :=
      (h.affine_integrable 1).bdd_mul he_meas he_bound
    have hminusInt : Integrable
        (fun x : ℝ => e x * complexFunction φ (2 * x - 1)) := by
      convert (h.affine_integrable (-1)).bdd_mul he_meas he_bound using 1
      funext x
      congr 2
    change (∫ x : ℝ, e x *
      ((k : ℂ) * (complexFunction φ (2 * x + 1) -
        complexFunction φ (2 * x - 1)))) = _
    rw [show (fun x : ℝ => e x *
        ((k : ℂ) * (complexFunction φ (2 * x + 1) -
          complexFunction φ (2 * x - 1)))) =
      fun x : ℝ => (k : ℂ) *
        (e x * complexFunction φ (2 * x + 1) -
          e x * complexFunction φ (2 * x - 1)) by
        funext x
        ring]
    rw [integral_const_mul, integral_sub hplus hminusInt]
    dsimp [e]
    have hplusFourier :
        (∫ a : ℝ, Complex.exp (((-2 * Real.pi * a * z : ℝ) : ℂ) * Complex.I) *
            complexFunction φ (2 * a + 1)) =
          𝓕 (fun x : ℝ => complexFunction φ (2 * x + 1)) z := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp only [smul_eq_mul]
    have hminusFourier :
        (∫ a : ℝ, Complex.exp (((-2 * Real.pi * a * z : ℝ) : ℂ) * Complex.I) *
            complexFunction φ (2 * a - 1)) =
          𝓕 (fun x : ℝ => complexFunction φ (2 * x - 1)) z := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp only [smul_eq_mul]
    rw [hplusFourier, hminusFourier]
  have hminus : (fun x : ℝ => complexFunction φ (2 * x - 1)) =
      fun x : ℝ => complexFunction φ (2 * x + (-1)) := by
    funext x
    congr 1
  rw [hleft, affine_fourier (φ := φ) 1 z, hminus,
    affine_fourier (φ := φ) (-1) z] at hfourier
  rw [h.scale_eq_two] at hfourier
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  push_cast at hfourier
  have hfourier' :
      2 * (1 / 2 * Complex.exp (Real.pi * Complex.I * (z : ℂ)) *
          originalFourier φ (z / 2) -
        1 / 2 * Complex.exp (-(Real.pi * Complex.I * (z : ℂ))) *
          originalFourier φ (z / 2)) =
      2 * Real.pi * Complex.I * (z : ℂ) * originalFourier φ z := by
    simpa [originalFourier] using hfourier
  have heq0 :
      Complex.exp ((Real.pi * (z : ℂ)) * Complex.I) -
          Complex.exp (-((Real.pi * (z : ℂ)) * Complex.I)) =
        2 * Complex.I * Complex.sin (Real.pi * (z : ℂ)) := by
    rw [Complex.sin]
    field_simp
    rw [Complex.I_sq]
    ring
  have heq :
      Complex.exp (Real.pi * Complex.I * (z : ℂ)) -
          Complex.exp (-(Real.pi * Complex.I * (z : ℂ))) =
        2 * Complex.I * Complex.sin (Real.pi * (z : ℂ)) := by
    convert heq0 using 1
    all_goals ring_nf
  have hrefine :
      (2 * Complex.I) *
          (Complex.sin (Real.pi * (z : ℂ)) * originalFourier φ (z / 2)) =
        (2 * Complex.I) *
          ((Real.pi * (z : ℂ)) * originalFourier φ z) := by
    calc
      (2 * Complex.I) *
          (Complex.sin (Real.pi * (z : ℂ)) * originalFourier φ (z / 2)) =
        (2 * Complex.I * Complex.sin (Real.pi * (z : ℂ))) *
          originalFourier φ (z / 2) := by ring
      _ = (Complex.exp (Real.pi * Complex.I * (z : ℂ)) -
          Complex.exp (-(Real.pi * Complex.I * (z : ℂ)))) *
            originalFourier φ (z / 2) := by rw [heq]
      _ = (2 * Complex.I) *
          ((Real.pi * (z : ℂ)) * originalFourier φ z) := by
        linear_combination hfourier'
  have hcancel :
      Complex.sin (Real.pi * (z : ℂ)) * originalFourier φ (z / 2) =
        (Real.pi * (z : ℂ)) * originalFourier φ z := by
    exact mul_left_cancel₀ (by exact mul_ne_zero (by norm_num) Complex.I_ne_zero) hrefine
  rw [complexSinc, if_neg (mul_ne_zero hpi hzC)]
  calc
    originalFourier φ z =
        (Complex.sin (Real.pi * (z : ℂ)) * originalFourier φ (z / 2)) /
          (Real.pi * (z : ℂ)) := by
      apply (eq_div_iff (mul_ne_zero hpi hzC)).2
      simpa [mul_comm] using hcancel.symm
    _ = Complex.sin (Real.pi * (z : ℂ)) / (Real.pi * (z : ℂ)) *
        originalFourier φ (z / 2) := by ring

/-- Iterating the refinement equation `N` times separates the first `N` sinc
factors from a Fourier-transform tail at the rescaled frequency `z / 2^N`. -/
theorem originalFourier_finite_product (z : ℝ) (N : ℕ) :
    originalFourier φ z =
      (∏ n ∈ Finset.range N,
        complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n)) *
          originalFourier φ (z / (2 : ℝ) ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        originalFourier φ z =
            (∏ n ∈ Finset.range N,
              complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n)) *
                originalFourier φ (z / (2 : ℝ) ^ N) := ih
        _ = (∏ n ∈ Finset.range N,
              complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n)) *
                (complexSinc
                    (Real.pi * ((z / (2 : ℝ) ^ N : ℝ) : ℂ)) *
                  originalFourier φ ((z / (2 : ℝ) ^ N) / 2)) := by
            rw [h.originalFourier_scaling]
        _ = (∏ n ∈ Finset.range (N + 1),
              complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n)) *
                originalFourier φ (z / (2 : ℝ) ^ (N + 1)) := by
            rw [Finset.prod_range_succ]
            have hfactor :
                complexSinc (Real.pi * ((z / (2 : ℝ) ^ N : ℝ) : ℂ)) =
                  complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ N) := by
              congr 1
              push_cast
              ring
            have htail : (z / (2 : ℝ) ^ N) / 2 =
                z / (2 : ℝ) ^ (N + 1) := by
              rw [pow_succ]
              ring
            rw [hfactor, htail]
            ring

/-- The Fourier transform of every function satisfying the original
characterization is the same infinite sinc product. -/
theorem originalFourier_eq_product (z : ℝ) :
    originalFourier φ z = rvachevFourierProduct z := by
  have hargs : Tendsto (fun N : ℕ => z / (2 : ℝ) ^ N) atTop (nhds 0) := by
    have hpow : Tendsto (fun N : ℕ => ((2 : ℝ)⁻¹) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    simpa [div_eq_mul_inv] using hpow.const_mul z
  have htail0 : Tendsto
      (fun N : ℕ => originalFourier φ (z / (2 : ℝ) ^ N)) atTop
        (nhds (originalFourier φ 0)) := by
    have hcont : Tendsto (originalFourier φ) (nhds 0)
        (nhds (originalFourier φ 0)) :=
      h.originalFourier_continuous.continuousAt
    exact hcont.comp hargs
  have htail : Tendsto
      (fun N : ℕ => originalFourier φ (z / (2 : ℝ) ^ N)) atTop (nhds 1) := by
    simpa [h.originalFourier_zero] using htail0
  have hmult : Multipliable fun n : ℕ =>
      complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n) :=
    sincFactors_multipliable z
  have hprod : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N,
        complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n)) atTop
      (nhds (∏' n : ℕ,
        complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n))) :=
    hmult.tendsto_prod_tprod_nat
  have hmul := hprod.mul htail
  have hlim : Tendsto (fun _N : ℕ => originalFourier φ z) atTop
      (nhds (∏' n : ℕ,
        complexSinc (Real.pi * (z : ℂ) / (2 : ℂ) ^ n))) := by
    simpa only [mul_one] using hmul.congr'
      (Filter.Eventually.of_forall fun N =>
        (h.originalFourier_finite_product z N).symm)
  unfold rvachevFourierProduct
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- Any two functions satisfying the original characterization have identical
Fourier transforms, even when their dilation constants are presented
independently. -/
theorem originalFourier_eq_of_isOriginalFabius {ψ : ℝ → ℝ} {ℓ : ℝ}
    (hψ : IsOriginalFabius ψ ℓ) (z : ℝ) :
    originalFourier φ z = originalFourier ψ z := by
  rw [h.originalFourier_eq_product, hψ.originalFourier_eq_product]

private noncomputable def schwartzMap : 𝓢(ℝ, ℂ) :=
  h.complex_hasCompactSupport.toSchwartzMap h.complex_contDiff

/-- Fourier injectivity makes the function in the original characterization
unique, independently of the initially unspecified constants. -/
theorem eq_of_isOriginalFabius {ψ : ℝ → ℝ} {ℓ : ℝ}
    (hψ : IsOriginalFabius ψ ℓ) : φ = ψ := by
  have htransform : 𝓕 h.schwartzMap = 𝓕 hψ.schwartzMap := by
    ext z
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    change originalFourier φ z = originalFourier ψ z
    exact h.originalFourier_eq_of_isOriginalFabius hψ z
  have hschwartz : h.schwartzMap = hψ.schwartzMap :=
    (FourierTransform.fourierEquiv ℂ 𝓢(ℝ, ℂ)).injective htransform
  funext x
  have hx := congrArg (fun s : 𝓢(ℝ, ℂ) => s x) hschwartz
  change (φ x : ℂ) = (ψ x : ℂ) at hx
  exact_mod_cast hx

/-- Every original solution is the canonical Rvachev function.  This
namespace form is convenient when the dilation constant is not otherwise
needed. -/
theorem eq_canonical : φ = rvachevUp fabius :=
  h.eq_of_isOriginalFabius canonical_isOriginalFabius

/-- Every original solution is even.  This is transported from the canonical
Rvachev function after uniqueness has been established. -/
theorem even : Function.Even φ := by
  rw [h.eq_canonical]
  exact rvachevUp_even fabius

/-- The functions and dilation constants of any two original solutions agree
simultaneously. -/
theorem pair_eq_of_isOriginalFabius {ψ : ℝ → ℝ} {ℓ : ℝ}
    (hψ : IsOriginalFabius ψ ℓ) : (φ, k) = (ψ, ℓ) := by
  apply Prod.ext
  · exact h.eq_of_isOriginalFabius hψ
  · exact h.scale_eq_two.trans hψ.scale_eq_two.symm

end IsOriginalFabius

/-- Every solution of the original problem is the canonical Rvachev
function, and its dilation constant is `2`. -/
theorem originalFabius_eq_canonical {φ : ℝ → ℝ} {k : ℝ}
    (h : IsOriginalFabius φ k) : φ = rvachevUp fabius ∧ k = 2 := by
  exact ⟨h.eq_canonical, h.scale_eq_two⟩

/-- Exact classification of the original compact-support solutions by the
canonical Rvachev function and the forced scale. -/
theorem isOriginalFabius_iff_eq_canonical (φ : ℝ → ℝ) (k : ℝ) :
    IsOriginalFabius φ k ↔ φ = rvachevUp fabius ∧ k = 2 := by
  constructor
  · exact originalFabius_eq_canonical
  · rintro ⟨rfl, rfl⟩
    exact canonical_isOriginalFabius

/-- Folding a bounded candidate forgets exactly its values strictly to the
right of one.  This result belongs conceptually next to `rvachevUp` in
`Basic.lean`; it is kept here to avoid invalidating the full foundational
import graph for a new, non-duplicated declaration. -/
theorem rvachevUp_eq_iff_eqOn_Iic_one (F G : BoundedFabius) :
    rvachevUp F = rvachevUp G ↔
      Set.EqOn (fabiusReal F) (fabiusReal G) (Set.Iic (1 : ℝ)) := by
  constructor
  · intro h t ht
    have hpoint := congrFun h (t - 1)
    have hnonpos : t - 1 ≤ 0 := sub_nonpos.mpr ht
    rw [rvachevUp_of_nonpos F hnonpos,
      rvachevUp_of_nonpos G hnonpos] at hpoint
    simpa only [sub_add_cancel] using hpoint
  · intro h
    funext x
    by_cases hx : x ≤ 0
    · rw [rvachevUp_of_nonpos F hx, rvachevUp_of_nonpos G hx]
      exact h (by
        change x + 1 ≤ 1
        linarith)
    · have hxpos : 0 < x := lt_of_not_ge hx
      rw [rvachevUp_of_pos F hxpos, rvachevUp_of_pos G hxpos]
      exact h (by
        change 1 - x ≤ 1
        linarith)

/-- A bounded candidate satisfies the Fabius characterization exactly when
its fold satisfies Rvachev's original characterization and its omitted open
right tail is constantly one.  The strict inequality is sharp: the fold still
observes the value at one through its value at zero. -/
theorem isFabius_iff_isOriginalFabius_rvachevUp_and_rightTail
    (F : BoundedFabius) :
    IsFabius F ↔
      IsOriginalFabius (rvachevUp F) 2 ∧
        ∀ x : ℝ, 1 < x → fabiusReal F x = 1 := by
  constructor
  · intro hF
    exact ⟨hF.isOriginalFabius_rvachevUp,
      fun x hx => hF.one_of_one_le x hx.le⟩
  · rintro ⟨hO, htail⟩
    have hup : rvachevUp F = rvachevUp fabius := hO.eq_canonical
    have hleft : Set.EqOn (fabiusReal F) (fabiusReal fabius)
        (Set.Iic (1 : ℝ)) :=
      (rvachevUp_eq_iff_eqOn_Iic_one F fabius).mp hup
    have hF_eq : F = fabius := by
      funext x
      apply Subtype.ext
      change fabiusReal F x = fabiusReal fabius x
      by_cases hx : x ≤ 1
      · exact hleft hx
      · have hx' : 1 < x := lt_of_not_ge hx
        rw [htail x hx', fabius_spec.one_of_one_le x hx'.le]
    rw [hF_eq]
    exact fabius_spec

/-- Original compact-support solutions are exactly the folds of bounded
Fabius solutions, with scale two; the bounded witness is unique. -/
theorem isOriginalFabius_iff_existsUnique_isFabius
    (φ : ℝ → ℝ) (k : ℝ) :
    IsOriginalFabius φ k ↔
      k = 2 ∧ ∃! F : BoundedFabius,
        IsFabius F ∧ φ = rvachevUp F := by
  constructor
  · intro h
    refine ⟨h.scale_eq_two, fabius, ⟨fabius_spec, h.eq_canonical⟩, ?_⟩
    intro G hG
    exact hG.1.eq fabius_spec
  · rintro ⟨hk, F, ⟨hF, hφ⟩, _⟩
    rw [hk, hφ]
    exact hF.isOriginalFabius_rvachevUp

/-- The exact existence-and-uniqueness formulation of Theorem 1 of
arXiv:1702.05442. -/
theorem existsUnique_originalFabius :
    ∃! p : (ℝ → ℝ) × ℝ, IsOriginalFabius p.1 p.2 := by
  refine ⟨(rvachevUp fabius, 2), canonical_isOriginalFabius, ?_⟩
  rintro ⟨φ, k⟩ h
  exact h.pair_eq_of_isOriginalFabius canonical_isOriginalFabius

end

end Fabius
