/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements unchanged. Prove finite regularity below infinity explicitly. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.JointBooleanRegularizationChoice
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
import OAI.Combinatorics.Progressions.Polynomial.SlicedPrincipalPolynomial

namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [Fintype O]

theorem selectedDerivative_fderiv_eq (U : (I → ℝ) → (O → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (x : I → ℝ)
    (hU : DifferentiableAt ℝ (fderiv ℝ U) x) :
    fderiv ℝ (selectedDerivative U J) x =
      (operatorPrecompose J).comp (fderiv ℝ (fderiv ℝ U) x) := by
  let L : ((I → ℝ) →L[ℝ] (O → ℝ)) →L[ℝ] ((O → ℝ) →L[ℝ] (O → ℝ)) := operatorPrecompose J
  change fderiv ℝ (L ∘ fderiv ℝ U) x = _
  rw [fderiv_comp x L.differentiableAt hU, L.fderiv]

theorem selectedDerivative_second_error (U V : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (hJ : ‖J‖ ≤ 1) (x : I → ℝ) :
    ‖fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ := by
  have hU' : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hV' : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  rw [selectedDerivative_fderiv_eq V J x (hV'.differentiable one_ne_zero x),
    selectedDerivative_fderiv_eq U J x (hU'.differentiable one_ne_zero x),
    ← ContinuousLinearMap.comp_sub]
  have hL : ‖operatorPrecompose (Y := O → ℝ) J‖ ≤ 1 := (operatorPrecompose_norm_le J).trans hJ
  calc
    _ ≤ ‖operatorPrecompose J‖ * ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ :=
      mul_le_mul_of_nonneg_right hL
        (norm_nonneg (fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x))
    _ = _ := one_mul _

theorem selectedDerivative_bound_of_second_error (U V : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (hJ : ‖J‖ ≤ 1) (x : I → ℝ)
    {H E : ℝ} (hH : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hE : ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ E) :
    ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H + E := by
  have ht := norm_add_le (fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x)
    (fderiv ℝ (selectedDerivative U J) x)
  have he : fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x +
      fderiv ℝ (selectedDerivative U J) x = fderiv ℝ (selectedDerivative V J) x := by
    ext y z i
    simp
  rw [he] at ht
  exact ht.trans ((add_le_add ((selectedDerivative_second_error U V hU hV J hJ x).trans hE) hH).trans_eq
    (add_comm E H))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem selected_cutoff_comparison_of_close_derivatives
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (κ → ℝ)) [IsProbabilityMeasure μ]
    (χ w : (κ → ℝ) → ℝ) (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure volume w = realDensityMeasure μ χ)
    (U V : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hJ : ‖J‖ ≤ 1) (K H S : ℝ≥0)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hsmall : ∀ x ∈ tsupport w, (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ 1 / 2)
    (hHU : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hHV : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H)
    (hS : (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) ≤ S)
    {ε η : ℝ} (hε : 0 < ε) (hmass : 1 - η ≤ ∫ x, w x)
    (hclose : ∀ x, w x ≠ 0 → dist (U x) (V x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    let B := 1 + 2 * (K : ℝ) * S + (Fintype.card κ : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt (B * ε) := by
  have hwi : Integrable w := hw.continuous.integrable_of_hasCompactSupport hs
  have hmass1 : (∫ x, |w x|) ≤ 1 := by
    have ht := cutoffMeasure_mass_le_one μ χ hχ hχ01
    rw [← hlaw, realDensityMeasure_real_univ volume w hwi hw0] at ht
    have he (x) : |w x| = w x := abs_of_nonneg (hw0 x)
    simpa only [he] using ht
  have hv (x) (hx : x ∈ tsupport w) :
      (selectedDerivative V J x).IsInvertible ∧ ‖(selectedDerivative V J x).inverse‖ ≤ 2 * K := by
    apply selected_inverse_perturbation U V J x (hinv x hx) K (hK x hx)
    apply le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)) K.coe_nonneg)
    simpa only [mul_one] using hsmall x hx
  let B : ℝ≥0 := 1 + (2 * K) * S + (Fintype.card κ : ℝ≥0) * ((2 * K) ^ 2 * H)
  have hB : 0 < (B : ℝ) := by dsimp only [B]; positivity
  have hbudget : ((2 * K : ℝ≥0) : ℝ) * S +
      (Fintype.card κ : ℝ) * (((2 * K : ℝ≥0) : ℝ) ^ 2 * H) ≤ B := by
    simp only [B, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_ofNat, NNReal.coe_one]
    linarith
  have hTU := imageTranslationBound_of_inverse_budget U hU J hJ w hw hs hw0 hmass1
    (2 * K) H S B hinv (fun x hx => (hK x hx).trans (by
      change (K : ℝ) ≤ 2 * K
      linarith [K.coe_nonneg])) hHU hS hbudget
  have hTV := imageTranslationBound_of_inverse_budget V hV J hJ w hw hs hw0 hmass1
    (2 * K) H S B (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2) hHV hS hbudget
  rw [hlaw] at hTU hTV
  have hc : ∀ᵐ x ∂realDensityMeasure μ χ, dist (U x) (V x) ≤ ε := by
    rw [← hlaw]
    exact ae_realDensityMeasure_of_forall_nonzero volume w hw.continuous.measurable _ hclose
  have ht := cutoff_box_image_comparison_sqrt μ χ hχ hχ01 U V hU.continuous.measurable
    hV.continuous.measurable B hB hTU hTV hε
    (cutoff_loss_of_density_mass μ volume χ w hχ hχ01 hwi hw0 hlaw hmass) hc φ hφ hbound
  simpa only [B, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
    NNReal.coe_ofNat, NNReal.coe_one] using ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPrincipalComparisonBudget (N m : ℕ) (C A r κ : ℝ) : ℝ :=
  1 + 2 * κ⁻¹ * (2 * (N : ℝ) ^ 2 * A / r) +
    N * ((2 * κ⁻¹) ^ 2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1))

theorem slicedPrincipalComparisonBudget_nonneg (N m : ℕ) {C A r κ : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) :
    0 ≤ slicedPrincipalComparisonBudget N m C A r κ := by
  unfold slicedPrincipalComparisonBudget
  positivity

theorem jointSlicedPrincipal_unitBox_comparison
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
    (b : ∀ d, B d) (i : ∀ d, F d) {m : ℕ}
    (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    (hwidth : ∀ d p, |lower d p| + |width d p| ≤ 1)
    {C a δ r κ ε : ℝ} (hC : 0 ≤ C) (hc : ∀ d, (∑ b, |c d b|) ≤ C)
    (ha : 0 < a) (hδ : 0 < δ) (hr : 0 < r) (hκ : 0 < κ)
    (hprincipal : ∀ d, a ≤ |c d (b d)|)
    (hselectedWidth : ∀ d j, δ ≤ width d (b d, j))
    (hselectedLower : ∀ d j, j ≠ i d → 0 ≤ lower d (b d, j))
    (hminor : ∀ d, κ ≤ a * δ * (δ * r) ^ (Fintype.card (F d) - 1))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ))
    (hV : ContDiff ℝ 2 V) (hε : 0 < ε) (hεone : ε ≤ 1) (hsmall : κ⁻¹ * ε ≤ 1 / 2)
    (herr : ∀ x, (∀ p, |x p| ≤ 1) →
      ‖V x - jointSlicedPrincipal c lower width x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤ ε)
    (φ : ((Σ _d : D, Unit) → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let N := Fintype.card (Σ d, B d × F d)
    |mappedTest (unitBoxMeasure (Σ d, B d × F d)) (jointSlicedPrincipal c lower width) φ -
      mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤
      8 * N * r + 4 * (Fintype.card D : ℝ) *
        Real.sqrt (slicedPrincipalComparisonBudget N m C A r κ * ε) := by
  classical
  let N := Fintype.card (Σ d, B d × F d)
  let U := jointSlicedPrincipal c lower width
  let J := jointSlicedInjection b i
  let w := unitBoxInteriorCutoff (ι := Σ d, B d × F d) r
  let H₀ : ℝ := N * (N * ((m : ℝ) * ((m : ℝ) * C)))
  let K : ℝ≥0 := ⟨κ⁻¹, inv_nonneg.mpr hκ.le⟩
  let H : ℝ≥0 := ⟨H₀ + 1, by dsimp [H₀]; positivity⟩
  let S : ℝ≥0 := ⟨2 * (N : ℝ) ^ 2 * A / r, by positivity⟩
  have hU : ContDiff ℝ 2 U := (jointSlicedPrincipal_contDiff c lower width).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hJ : ‖J‖ ≤ 1 := jointSlicedInjection_norm_le b i
  have hbox (x) (hx : x ∈ tsupport w) : ∀ p, |x p| ≤ 1 := by
    intro p
    have hp := unitBoxInteriorCutoff_tsupport hr hx p
    rw [abs_of_nonneg (hr.le.trans hp.1)]
    linarith
  have hinv (x) (hx : x ∈ tsupport w) :
      (selectedDerivative U J x).IsInvertible ∧ ‖(selectedDerivative U J x).inverse‖ ≤ K := by
    apply jointSlicedPrincipal_inverse_bound c lower width b i x hκ
    intro d
    apply (hminor d).trans
    apply principalSliceSlope_lower (c d) (lower d) (width d) _ (b d) (i d)
      ha.le hδ.le hr.le (hprincipal d) (hselectedWidth d) (hselectedLower d)
    intro j _
    exact (unitBoxInteriorCutoff_tsupport hr hx ⟨d, b d, j⟩).1
  have hHU₀ (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H₀ := by
    have hsecond := (jointSlicedPrincipal_c2_bounds c lower width hdegree hwidth hC hc x (hbox x hx)).2.2
    have hUd : DifferentiableAt ℝ (fderiv ℝ U) x :=
      (hU.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiable one_ne_zero x
    rw [selectedDerivative_fderiv_eq U J x hUd]
    have hnonneg : 0 ≤ ‖fderiv ℝ (fderiv ℝ U) x‖ := ContinuousLinearMap.opNorm_nonneg _
    calc
      _ ≤ ‖operatorPrecompose J‖ * ‖fderiv ℝ (fderiv ℝ U) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ U) x‖ :=
        mul_le_mul_of_nonneg_right ((operatorPrecompose_norm_le J).trans hJ) hnonneg
      _ ≤ H₀ := by simpa only [one_mul] using hsecond
  have hHU (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H :=
    (hHU₀ x hx).trans (by change H₀ ≤ H₀ + 1; linarith)
  have hHV (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H :=
    (selectedDerivative_bound_of_second_error U V hU hV J hJ x (hHU₀ x hx)
      (herr x (hbox x hx)).2.2).trans (add_le_add le_rfl hεone)
  have h := selected_cutoff_comparison_of_close_derivatives
    (unitBoxMeasure (Σ d, B d × F d)) w w
    (unitBoxInteriorCutoff_contDiff r).continuous.measurable (unitBoxInteriorCutoff_range r)
    ((unitBoxInteriorCutoff_contDiff r).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num))
    (unitBoxInteriorCutoff_compact hr) (fun x => (unitBoxInteriorCutoff_range r x).1)
    (unitBoxInteriorCutoff_density hr) U V hU hV J hJ K H S
    (fun x hx => (hinv x hx).1) (fun x hx => (hinv x hx).2)
    (fun x hx => (mul_le_mul_of_nonneg_left (herr x (hbox x hx)).2.1 K.coe_nonneg).trans hsmall)
    hHU hHV (unitBoxInteriorCutoff_derivative_budget A hA hr) hε
    (unitBoxInteriorCutoff_mass hr)
    (fun x hx => by
      rw [dist_comm, dist_eq_norm]
      exact (herr x (hbox x (subset_tsupport w hx))).1) φ hφ hφone
  change |mappedTest (unitBoxMeasure (Σ d, B d × F d)) U φ -
      mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤
    2 * (4 * (N : ℝ) * r) + 4 * (Fintype.card (Σ _d : D, Unit) : ℝ) *
      Real.sqrt (slicedPrincipalComparisonBudget N m C A r κ * ε) at h
  have hcard : Fintype.card (Σ _d : D, Unit) = Fintype.card D := by simp
  rw [hcard] at h
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPrincipalBoundaryRadius (N : ℕ) (η : ℝ) : ℝ :=
  min (1 / 4) (η / (16 * ((N : ℝ) + 1)))

theorem slicedPrincipalBoundaryRadius_spec (N : ℕ) {η : ℝ} (hη : 0 < η) :
    let r := slicedPrincipalBoundaryRadius N η
    0 < r ∧ r ≤ 1 / 4 ∧ 8 * N * r ≤ η / 2 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := by dsimp [r, slicedPrincipalBoundaryRadius]; positivity
  have hr1 : r ≤ 1 / 4 := min_le_left _ _
  have he : r ≤ η / (16 * ((N : ℝ) + 1)) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((N : ℝ) + 1))).mp he
  refine ⟨hr, hr1, ?_⟩
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

noncomputable def slicedPrincipalC2Tolerance (N O m : ℕ) (C a δ A η : ℝ) : ℝ :=
  let r := slicedPrincipalBoundaryRadius N η
  let κ := a * δ * (δ * r) ^ m
  polynomialPerturbationScale κ⁻¹ 1 (slicedPrincipalComparisonBudget N m C A r κ) (η / 2) O

theorem slicedPrincipalC2Tolerance_spec
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    {m : ℕ} (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    {C a δ η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) :
    let t := slicedPrincipalC2Tolerance (Fintype.card (Σ d, B d × F d)) (Fintype.card D) m C a δ A η
    0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
      (b : ∀ d, B d) (i : ∀ d, F d),
      (∀ d p, |lower d p| + |width d p| ≤ 1) →
      (∀ d, (∑ b, |c d b|) ≤ C) → (∀ d, a ≤ |c d (b d)|) →
      (∀ d j, δ ≤ width d (b d, j)) →
      (∀ d j, j ≠ i d → 0 ≤ lower d (b d, j)) →
      ∀ V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ),
      ContDiff ℝ 2 V →
      (∀ x, (∀ p, |x p| ≤ 1) →
        ‖V x - jointSlicedPrincipal c lower width x‖ ≤ t ∧
        ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ t ∧
        ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤ t) →
      ∀ φ : ((Σ _d : D, Unit) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |mappedTest (unitBoxMeasure (Σ d, B d × F d)) (jointSlicedPrincipal c lower width) φ -
          mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤ η := by
  let N := Fintype.card (Σ d, B d × F d)
  let r := slicedPrincipalBoundaryRadius N η
  have hr := slicedPrincipalBoundaryRadius_spec N hη
  let κ := a * δ * (δ * r) ^ m
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr.1) _)
  have hdr : δ * r ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hδone (hr.2.1.trans (by norm_num)) hr.1.le zero_le_one
      _ = 1 := one_mul _
  let Q := slicedPrincipalComparisonBudget N m C A r κ
  have hQ : 0 ≤ Q := slicedPrincipalComparisonBudget_nonneg N m hC A.coe_nonneg hr.1 hκ
  let t := slicedPrincipalC2Tolerance N (Fintype.card D) m C a δ A η
  have ht := polynomialPerturbationScale_spec (inv_nonneg.mpr hκ.le) zero_le_one hQ
    (half_pos hη) (Fintype.card D)
  change 0 < t ∧ t ≤ 1 ∧ κ⁻¹ * (t * 1) ≤ 1 / 2 ∧ t * 1 ≤ 1 ∧
    4 * (Fintype.card D : ℝ) * Real.sqrt (Q * (t * (1 + 1))) ≤ η / 2 at ht
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro c lower width b i hwidth hc hprincipal hw hlower V hV herr φ hφ hφone
  have hminor (d) : κ ≤ a * δ * (δ * r) ^ (Fintype.card (F d) - 1) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (mul_pos hδ hr.1).le hdr ((Nat.sub_le _ _).trans (hdegree d)))
      (mul_pos ha hδ).le
  have h := jointSlicedPrincipal_unitBox_comparison c lower width b i hdegree hwidth hC hc
    ha hδ hr.1 hκ hprincipal hw hlower hminor A hA V hV ht.1 ht.2.1
    (by simpa only [mul_one] using ht.2.2.1) herr φ hφ hφone
  have hsqrt : 4 * (Fintype.card D : ℝ) * Real.sqrt (Q * t) ≤ η / 2 := by
    apply le_trans _ ht.2.2.2.2
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith [ht.1] : t ≤ t * (1 + 1)) hQ
  exact h.trans (by change 8 * (N : ℝ) * r + 4 * (Fintype.card D : ℝ) * Real.sqrt (Q * t) ≤ η; linarith [hr.2.2])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F]

theorem principalSliceValue_abs_le (c : B → ℝ) (lower width : B × F → ℝ)
    (hwidth : ∀ p, |lower p| + |width p| ≤ 1)
    (x : B × F → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    |principalSliceValue c lower width x| ≤ ∑ b, |c b| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [abs_mul, Finset.abs_prod]
  have hp : (∏ i : F, |lower (b,i) + width (b,i) * x (b,i)|) ≤ 1 := by
    apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
    intro i _
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact (add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) (hx _))).trans (hwidth _)
  exact mul_le_of_le_one_right (abs_nonneg _) hp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBoolean_good_weight_comparison {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (A T : ℝ≥0)
    (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)) (hV : ContDiff ℝ 2 V)
    (hsmall : ∀ x ∈ tsupport (jointBooleanGoodWeight c sets block v sel ψ r κ),
      (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ 1 / 2)
    (hHV : ∀ x ∈ tsupport (jointBooleanGoodWeight c sets block v sel ψ r κ),
      ‖fderiv ℝ (selectedDerivative V (jointBooleanInjection block v sel)) x‖ ≤ H)
    {ε η : ℝ} (hε : 0 < ε)
    (hmass : 1 - η ≤ ∫ x, jointBooleanGoodWeight c sets block v sel ψ r κ x)
    (hclose : ∀ x, jointBooleanGoodWeight c sets block v sel ψ r κ x ≠ 0 →
      dist (jointBooleanSampler h c sets x) (V x) ≤ ε)
    (φ : ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
    let Q := 1 + 2 * (K : ℝ) * S +
      (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
    |(∫ x, φ (jointBooleanSampler h c sets x) ∂jointBooleanSource h) -
      ∫ x, φ (V x) ∂jointBooleanSource h| ≤
      2 * η + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * ε) := by
  let S : ℝ≥0 := ⟨jointBooleanWeightBudget (O := O) (α := α) h C A T r κ,
    jointBooleanWeightBudget_nonneg h C hC A T r (fun d i => (hr d i).le) κ (fun d => (hκ d).le)⟩
  have hs := jointBooleanGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  have hi (x) (hx : x ∈ tsupport (jointBooleanGoodWeight c sets block v sel ψ r κ)) :=
    jointBoolean_selected_inverse_bound c sets block v sel hcard x C (fun _ => 1) κ hC
      (fun _ => zero_le_one) hκ hc (hs.2.2.2.2 x hx).1 (hs.2.2.2.2 x hx).2 K.coe_nonneg hK
  apply selected_cutoff_comparison_of_close_derivatives (jointBooleanSource h)
    (jointBooleanCutoff c sets block v sel ψ r κ) (jointBooleanGoodWeight c sets block v sel ψ r κ)
    (jointBooleanCutoff_contDiff c sets block v sel ψ hψ r κ).continuous.measurable
    (jointBooleanCutoff_range c sets block v sel ψ hrange r κ) hs.1 hs.2.1 hs.2.2.1
    (jointBooleanGoodWeight_measure c sets block v sel ψ hψ hrange hzero r hr κ hκ)
    (jointBooleanSampler h c sets) V ((jointBooleanSampler_contDiff h c sets).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)) hV
    (jointBooleanInjection block v sel) (jointBooleanInjection_norm_le block hblock v sel) K H S
    (fun x hx => (hi x hx).1) (fun x hx => (hi x hx).2) hsmall _ hHV _ hε hmass hclose φ hφ hbound
  · intro x hx
    exact jointBoolean_selected_derivative_bound c sets block v sel hcard x C (fun _ => 1) hC
      (fun _ => le_rfl) hc (hs.2.2.2.2 x hx).1 H.coe_nonneg hH
  · exact jointBooleanGoodWeight_derivative_budget c sets block v sel hcard C hC hc
      ψ hψ hrange hzero A T hLip hTransition r hr κ hκ

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem jointBoolean_c2_comparison
    {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (A T : ℝ≥0)
    (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)) (hV : ContDiff ℝ 2 V)
    {M t : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (herr : ∀ x, (∀ i, |x i| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ t * M ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ t * M ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ t * M)
    (hsmall : (K : ℝ) * (t * M) ≤ 1 / 2) (hsecond : t * M ≤ 1)
    {η : ℝ} (hmass : 1 - η ≤ ∫ x, jointBooleanGoodWeight c sets block v sel ψ r κ x)
    (φ : ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
    let Q := 1 + 2 * (K : ℝ) * S +
      (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * ((H : ℝ) + 1))
    |(∫ x, φ (jointBooleanSampler h c sets x) ∂jointBooleanSource h) -
      ∫ x, φ (V x) ∂jointBooleanSource h| ≤
      2 * η + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := by
  let U := jointBooleanSampler h c sets
  let w := jointBooleanGoodWeight c sets block v sel ψ r κ
  let J := jointBooleanInjection block v sel
  have hU : ContDiff ℝ 2 U := (jointBooleanSampler_contDiff h c sets).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hw := jointBooleanGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  have he (x) (hx : x ∈ tsupport w) := herr x (hw.2.2.2.2 x hx).1
  have hsmall' (x) (hx : x ∈ tsupport w) : (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (he x hx).2.1 K.coe_nonneg).trans hsmall
  have hHV (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ (H + 1 : ℝ≥0) := by
    have hHU := jointBoolean_selected_derivative_bound c sets block v sel hcard x C (fun _ => 1)
      hC (fun _ => le_rfl) hc (hw.2.2.2.2 x hx).1 H.coe_nonneg hH
    have hd := selectedDerivative_bound_of_second_error U V hU hV J
      (jointBooleanInjection_norm_le block hblock v sel) x hHU (he x hx).2.2
    exact hd.trans (add_le_add le_rfl hsecond)
  have hclose (x) (hx : w x ≠ 0) : dist (U x) (V x) ≤ t * (1 + M) := by
    rw [dist_comm, dist_eq_norm]
    exact (he x (subset_closure hx)).1.trans (by nlinarith)
  have heps : 0 < t * (1 + M) := mul_pos ht (by linarith)
  have hcap (d : D) : productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ (H + 1 : ℝ≥0) :=
    (hH d).trans (by simp)
  have hout := jointBoolean_good_weight_comparison c sets block hblock v sel hcard C hC hc
    ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K (H + 1) hK hcap
    V hV hsmall' hHV heps hmass hclose φ hφ hbound
  simpa only [NNReal.coe_add, NNReal.coe_one] using hout

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem exists_joint_boolean_stability
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (hsets : ∀ d, Function.Injective (sets d)) (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (block d o)|) (hcup : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition) :
    ∃ sel : ∀ d, O d → Option α, ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let v := fun d => (⟨0, hh d⟩ : Fin (h d))
      let w := jointBooleanGoodWeight c sets block v sel ψ r κ
      let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
      ∀ K H : ℝ≥0,
      (∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
        (h d) (C d) 1 (κ d) ≤ K) →
      (∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H) →
      ∀ V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ), ContDiff ℝ 2 V →
      (∀ x ∈ tsupport w, (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ 1 / 2) →
      (∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative V (jointBooleanInjection block v sel)) x‖ ≤ H) →
      ∀ ε : ℝ, 0 < ε → (∀ x, w x ≠ 0 → dist (jointBooleanSampler h c sets x) (V x) ≤ ε) →
      ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        let Q := 1 + 2 * (K : ℝ) * S +
          (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
        |(∫ x, φ (jointBooleanSampler h c sets x) ∂jointBooleanSource h) -
          ∫ x, φ (V x) ∂jointBooleanSource h| ≤
          2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * ε) := by
  obtain ⟨sel, hsel⟩ := exists_joint_boolean_good_region c sets hsets h hh hcard block hblock
    c₀ hc₀ hclow ψ hψ hrange hzero hone
  refine ⟨sel, ?_⟩
  intro η hη
  dsimp only
  intro K H hK hH V hV hsmall hHV ε hε hclose φ hφ hbound
  obtain ⟨hκ, _, _, _, hm, _, _⟩ := hsel η hη
  exact jointBoolean_good_weight_comparison c sets block hblock (fun d => ⟨0, hh d⟩) sel hcard
    C hC hcup ψ hψ hrange hzero A T hLip hTransition
    _ (fun d _ => scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d)))
    _ (fun d => (hκ d).1) K H hK hH V hV hsmall hHV hε hm hclose φ hφ hbound

end Erdos3

end

end OAI
