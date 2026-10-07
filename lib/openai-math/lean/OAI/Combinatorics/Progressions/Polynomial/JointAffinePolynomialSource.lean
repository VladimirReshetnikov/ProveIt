import OAI.Combinatorics.Progressions.Lattices.JointAffineBooleanTolerance

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z : Type*} [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

noncomputable def jointAffinePolynomialTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (degree : ℕ) (Cp δ E : ℝ) : ℝ :=
  jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ E /
    (1 + polynomialC2BoxBudget
      (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp)

theorem exists_uniform_joint_affine_polynomial_source_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffinePolynomialTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Cp δ E ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ p : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ,
    (∀ o i, (p o).degreeOf i ≤ degree) → (∀ o m, |(p o).coeff m| ≤ Cp) →
    ∀ z : Z → ℝ, (∀ i, |z i| ≤ 1) →
    parameterPolynomialMap p 0 z = jointBooleanSampler h c sets →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) ((parameterPolynomialMap p t z) ∘ slice) φ| ≤ E := by
  obtain ⟨ρ, hρ, hρone, hρeq, ε, hε, hεone, hεeq, hs⟩ := exists_uniform_joint_affine_source_tolerance_with_scales
    h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition δ hδ hδone hE
  let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp
  have hM : 0 ≤ M := polynomialC2BoxBudget_nonneg _ _ hCp
  let t := ε / (1 + M)
  have ht : 0 < t := div_pos hε (by positivity)
  have hte : t ≤ ε := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have htone : t ≤ 1 := hte.trans hεone
  have htM : t * M ≤ ε := by
    have he : t * (1 + M) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, ?_, ?_⟩
  · change ε / (1 + M) = _
    rw [hεeq]
    rfl
  intro c hclow hcup center width hw hwidth hbox
  have hd := hs c hclow hcup center width hw hwidth hbox
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_⟩
  intro p hpdeg hpcoeff z hz hpzero φ hφ hbound
  apply hd.2.2.2.2 (parameterPolynomialMap p t z)
    ((parameterPolynomialMap_contDiff p t z).of_le (by norm_num)) _ φ hφ hbound
  intro x hx
  have he := parameterPolynomialMap_uniform_c2_error p hpdeg hCp hpcoeff
    (show |t| ≤ 1 by rwa [abs_of_pos ht]) z hz x hx
  rw [hpzero, abs_of_pos ht] at he
  exact ⟨he.1.trans htM, he.2.1.trans htM, he.2.2.trans htM⟩

theorem exists_uniform_joint_affine_polynomial_source
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ p : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ,
    (∀ o i, (p o).degreeOf i ≤ degree) → (∀ o m, |(p o).coeff m| ≤ Cp) →
    ∀ z : Z → ℝ, (∀ i, |z i| ≤ 1) →
    parameterPolynomialMap p 0 z = jointBooleanSampler h c sets →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) ((parameterPolynomialMap p t z) ∘ slice) φ| ≤ E := by
  obtain ⟨ρ, hρ, hρone, _, t, ht, htone, _, hs⟩ :=
    exists_uniform_joint_affine_polynomial_source_with_scales (Z := Z)
      h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
      degree Cp hCp δ hδ hδone hE
  exact ⟨ρ, hρ, hρone, t, ht, htone, hs⟩

end Erdos3

end

end OAI
