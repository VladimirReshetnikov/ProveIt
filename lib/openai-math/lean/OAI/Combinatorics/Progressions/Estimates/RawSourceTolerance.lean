import OAI.Combinatorics.Progressions.Estimates.NestedDiracIntegral
import OAI.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialComparison
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleLowerBound
import OAI.Combinatorics.Progressions.Probability.RawSourceLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem coefficient_array_joint_comparison
    {D K Z α Y : Type*} [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z]
    [Fintype α] [DecidableEq α] [MeasurableSpace Y]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (block d o)|) (hcup : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, |c d b|) ≤ Csum) (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) :
    ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
      let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
        (degree + 2) (booleanJetMassBudget (Fintype.card α) degree Csum +
          booleanJetMassBudget (Fintype.card α) degree Wsum)
      ∀ Kinv Hderiv : ℝ≥0,
      (∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
        (h d) (C d) 1 (κ d) ≤ Kinv) →
      (∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ Hderiv) →
      ∀ t : ℝ, 0 < t → t ≤ 1 → (Kinv : ℝ) * (t * M) ≤ 1 / 2 → t * M ≤ 1 →
      ∀ μ : Measure (Z → ℝ), IsProbabilityMeasure μ → (∀ᵐ z ∂μ, ∀ j, |z j| ≤ 1) →
      ∀ P : (Z → ℝ) × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        let Q := 1 + 2 * (Kinv : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
          ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
        |(∫ p, φ (P (p.1, jointBooleanSampler h c sets p.2)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, coefficientArraySampler h c sets terms weight exponent
            coefficientIndex inputIndex t p.1 p.2)) ∂μ.prod (jointBooleanSource h)| ≤
          2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := by
  obtain ⟨sel, hsel⟩ := exists_joint_boolean_good_region c sets hsets h hh hcard block hblock
    c₀ hc₀ hclow ψ hψ hrange hzero hone
  intro η hη
  dsimp only
  intro Kinv Hderiv hK hH t ht ht1 hsmall hsecond μ hμ hbox P hP φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨hκ, _, _, _, hmass, _, _⟩ := hsel η hη
  let tail := jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex
  let p := jointBooleanPerturbedPolynomial h c sets tail
  have hb := coefficientArraySampler_polynomial_bounds h c sets terms weight exponent
    coefficientIndex inputIndex hdegree htaildegree hcsum hwsum
  have hCp : 0 ≤ booleanJetMassBudget (Fintype.card α) degree Csum +
      booleanJetMassBudget (Fintype.card α) degree Wsum :=
    add_nonneg (booleanJetMassBudget_nonneg _ _ hCsum) (booleanJetMassBudget_nonneg _ _ hWsum)
  have hV : Measurable (fun y : (Z → ℝ) × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t y.1 y.2) := by
    simp_rw [coefficientArraySampler_polynomial]
    exact (parameterPolynomialMap_joint_continuous _ _).measurable
  apply postprocessed_image_comparison_of_ae_fiber_bounds μ (jointBooleanSource h)
    (fun y => jointBooleanSampler h c sets y.2)
    (fun y => coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t y.1 y.2)
    ((jointBooleanSampler_contDiff h c sets).continuous.measurable.comp measurable_snd)
    hV ?_ P hP φ hφ hbound
  filter_upwards [hbox] with z hz
  intro f hf hfb
  rw [coefficientArraySampler_polynomial]
  exact jointBoolean_polynomial_comparison c sets block hblock (fun d => ⟨0, hh d⟩) sel hcard
    C hC hcup ψ hψ hrange hzero A T hLip hTransition
    _ (fun d _ => scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d)))
    _ (fun d => (hκ d).1) Kinv Hderiv hK hH p hb.1 hCp hb.2 z hz
    (jointBooleanPerturbedPolynomial_zero h c sets tail z) ht ht1 hsmall hsecond hmass f hf hfb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem coefficient_array_fiber_comparison
    {D K Z α : Type*} [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z]
    [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (block d o)|) (hcup : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, |c d b|) ≤ Csum) (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) :
    ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
      let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
        (degree + 2) (booleanJetMassBudget (Fintype.card α) degree Csum +
          booleanJetMassBudget (Fintype.card α) degree Wsum)
      ∀ Kinv Hderiv : ℝ≥0,
      (∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
        (h d) (C d) 1 (κ d) ≤ Kinv) →
      (∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ Hderiv) →
      ∀ t : ℝ, 0 < t → t ≤ 1 → (Kinv : ℝ) * (t * M) ≤ 1 / 2 → t * M ≤ 1 →
      ∀ z : Z → ℝ, (∀ j, |z j| ≤ 1) →
      ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        let Q := 1 + 2 * (Kinv : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
          ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
        |(∫ x, φ (jointBooleanSampler h c sets x) ∂jointBooleanSource h) -
          ∫ x, φ (coefficientArraySampler h c sets terms weight exponent
            coefficientIndex inputIndex t z x) ∂jointBooleanSource h| ≤
          2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := by
  intro η hη
  dsimp only
  intro Kinv Hderiv hK hH t ht ht1 hsmall hsecond z hz φ hφ hbound
  have hbox : ∀ᵐ y ∂Measure.dirac z, ∀ j, |y j| ≤ 1 := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hz
  have he := coefficient_array_joint_comparison c sets hsets h hh hcard block hblock c₀ C hc₀ hC
    hclow hcup ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex
    inputIndex hdegree htaildegree hCsum hWsum hcsum hwsum η hη Kinv Hderiv hK hH t ht ht1
    hsmall hsecond (Measure.dirac z) (by infer_instance) hbox Prod.snd measurable_snd φ hφ hbound
  have hU : Measurable (fun y : (Z → ℝ) × (JointBlockParameter B h α → ℝ) =>
      jointBooleanSampler h c sets y.2) :=
    (jointBooleanSampler_contDiff h c sets).continuous.measurable.comp measurable_snd
  have hV : Measurable (fun y : (Z → ℝ) × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t y.1 y.2) := by
    simp_rw [coefficientArraySampler_polynomial]
    exact (parameterPolynomialMap_joint_continuous _ _).measurable
  have hIU := integral_dirac_first (jointBooleanSource h) z
    (fun y => φ (jointBooleanSampler h c sets y.2)) (hφ.comp hU)
  have hIV := integral_dirac_first (jointBooleanSource h) z
    (fun y => φ (coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t y.1 y.2))
    (hφ.comp hV)
  dsimp only at he
  rw [hIU, hIV] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem random_coefficient_array_joint_comparison
    {Ω D K Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) :
    ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
      let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
        (degree + 2) (booleanJetMassBudget (Fintype.card α) degree Csum +
          booleanJetMassBudget (Fintype.card α) degree Wsum)
      ∀ Kinv Hderiv : ℝ≥0,
      (∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
        (h d) (C d) 1 (κ d) ≤ Kinv) →
      (∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ Hderiv) →
      ∀ t : ℝ, 0 < t → t ≤ 1 → (Kinv : ℝ) * (t * M) ≤ 1 / 2 → t * M ≤ 1 →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        let Q := 1 + 2 * (Kinv : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
          ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
        |(∫ p, φ (P (p.1, jointBooleanSampler h (c p.1) sets p.2)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, coefficientArraySampler h (c p.1) sets terms weight exponent
            coefficientIndex inputIndex t (z p.1) p.2)) ∂μ.prod (jointBooleanSource h)| ≤
          2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := by
  intro η hη
  dsimp only
  intro Kinv Hderiv hK hH t ht ht1 hsmall hsecond μ hμ hbox hclow hcup hcsum P hP φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  have hU : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      jointBooleanSampler h (c p.1) sets p.2) :=
    jointBooleanSampler_measurable_frozen h sets c hc
  have hV : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h (c p.1) sets terms weight exponent coefficientIndex inputIndex t
        (z p.1) p.2) :=
    coefficientArraySampler_measurable_frozen h sets terms weight exponent coefficientIndex inputIndex t c hc z hz
  apply postprocessed_image_comparison_of_ae_fiber_bounds μ (jointBooleanSource h) _ _ hU hV ?_ P hP φ hφ hbound
  filter_upwards [hbox, hclow, hcup, hcsum] with a ha hlowa hupa hsuma
  intro f hf hfb
  exact coefficient_array_fiber_comparison (c a) sets hsets h hh hcard block hblock c₀ C hc₀ hC
    hlowa hupa ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex
    inputIndex hdegree htaildegree hCsum hWsum hsuma hwsum η hη Kinv Hderiv hK hH t ht ht1
    hsmall hsecond (z a) ha f hf hfb

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def booleanRegularizationRadius {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c₀ C : D → ℝ) (A T : ℝ≥0) (ε : ℝ) : ℝ :=
  regularizationRadius
    (jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T
      (fun _ => ε/(4*((Fintype.card D : ℝ)+1)))) ε

noncomputable def booleanToleranceMinor {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)]
    (h : D → ℕ) (c₀ : D → ℝ) (ε : ℝ) (d : D) : ℝ :=
  canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) ((ε/4)/((Fintype.card D : ℝ)+1))

noncomputable def booleanToleranceBoundary {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (ε : ℝ) (d : D)
    (_ : B d × Fin (h d)) : ℝ :=
  scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (((ε/4)/((Fintype.card D : ℝ)+1))/2)

noncomputable def booleanToleranceC2 {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (Csum Wsum : ℝ) : ℝ :=
  polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
    (degree+2) (booleanJetMassBudget (Fintype.card α) degree Csum+
      booleanJetMassBudget (Fintype.card α) degree Wsum)

noncomputable def booleanToleranceDivergence {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c₀ C : D → ℝ) (A T : ℝ≥0) (ε : ℝ) : ℝ :=
  let κ := booleanToleranceMinor (O := O) (α := α) h c₀ ε
  let K := jointBooleanInverseBudget (O := O) (α := α) h C κ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let S := jointBooleanWeightBudget (O := O) (α := α) h C A T
    (booleanToleranceBoundary (B := B) (α := α) h ε) κ
  1+2*(K : ℝ)*S+(Fintype.card (JointBlockParameter B h α) : ℝ)*((2*(K : ℝ))^2*((H : ℝ)+1))

noncomputable def booleanPerturbationScale {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (Z : Type*) [Fintype Z] (h : D → ℕ) (c₀ C : D → ℝ) (A T : ℝ≥0)
    (degree : ℕ) (Csum Wsum ε : ℝ) : ℝ :=
  polynomialPerturbationScale
    (jointBooleanInverseBudget (O := O) (α := α) h C (booleanToleranceMinor (O := O) (α := α) h c₀ ε))
    (booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum)
    (booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A T ε)
    (ε/2) (Fintype.card (Σ d, O d))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem booleanToleranceMinor_pos {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d)
    {ε : ℝ} (hε : 0 < ε) (d : D) :
    0 < booleanToleranceMinor (O := O) (α := α) h c₀ ε d :=
  canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (by positivity)

theorem booleanToleranceBoundary_pos {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) {ε : ℝ} (hε : 0 < ε)
    (d : D) (i : B d × Fin (h d)) :
    0 < booleanToleranceBoundary (B := B) (α := α) h ε d i :=
  scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (by positivity)

theorem booleanToleranceC2_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum) :
    0 ≤ booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum :=
  polynomialC2BoxBudget_nonneg _ _
    (add_nonneg (booleanJetMassBudget_nonneg _ _ hCsum) (booleanJetMassBudget_nonneg _ _ hWsum))

theorem booleanToleranceDivergence_nonneg {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (A T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A T ε := by
  have hS := jointBooleanWeightBudget_nonneg (O := O) (α := α) h C hC A T
    (booleanToleranceBoundary (B := B) (α := α) h ε)
    (fun d i => (booleanToleranceBoundary_pos h hε d i).le)
    (booleanToleranceMinor (O := O) (α := α) h c₀ ε)
    (fun d => (booleanToleranceMinor_pos h hh c₀ hc₀ hε d).le)
  dsimp only [booleanToleranceDivergence]
  positivity

theorem booleanRegularizationRadius_inverse_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c₀ C : D → ℝ) (A T : ℝ≥0) {ε P : ℝ}
    (hε : 0 < ε) (hP : 0 ≤ P)
    (hL : (jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T
      (fun _ => ε/(4*((Fintype.card D : ℝ)+1))) : ℝ) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    (booleanRegularizationRadius (B := B) (O := O) (α := α) h c₀ C A T ε)⁻¹ ≤ Real.exp (2*P+2) :=
  regularizationRadius_inverse_le_exp (by positivity) hε hP hL hεP

theorem booleanPerturbationScale_inverse_le_exp {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (Z : Type*) [Fintype Z] (h : D → ℕ) (hh : ∀ d, 0 < h d) (c₀ C : D → ℝ)
    (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d) (A T : ℝ≥0) (degree : ℕ)
    {Csum Wsum ε P : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum) (hε : 0 < ε) (hP : 0 ≤ P)
    (hm : (Fintype.card (Σ d, O d) : ℝ) ≤ Real.exp P)
    (hK : (jointBooleanInverseBudget (O := O) (α := α) h C
      (booleanToleranceMinor (O := O) (α := α) h c₀ ε) : ℝ) ≤ Real.exp P)
    (hM : booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum ≤ Real.exp P)
    (hQ : booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A T ε ≤ Real.exp P)
    (hεP : (ε/2)⁻¹ ≤ Real.exp P) :
    (booleanPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Csum Wsum ε)⁻¹ ≤
      Real.exp (6*P+8) :=
  polynomialPerturbationScale_inverse_le_exp (by positivity)
    (booleanToleranceC2_nonneg Z h degree hCsum hWsum)
    (booleanToleranceDivergence_nonneg h hh c₀ C hc₀ hC A T hε)
    (half_pos hε) hP _ hm hK hM hQ hεP

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_random_coefficient_array_tolerance_with_scale
    {Ω D K Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Csum Wsum ε ∧
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, jointBooleanSampler h (c p.1) sets p.2)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, coefficientArraySampler h (c p.1) sets terms weight exponent
            coefficientIndex inputIndex t (z p.1) p.2)) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  let η : D → ℝ := fun _ => (ε / 4) / ((Fintype.card D : ℝ) + 1)
  have hη (d : D) : 0 < η d := by dsimp [η]; positivity
  have hsum : (∑ d, η d) ≤ ε / 4 := by
    simp only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
  have hκ (d : D) : 0 < κ d := canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (hη d)
  let r := fun d (_ : B d × Fin (h d)) =>
    scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  have hr (d : D) (i : B d × Fin (h d)) : 0 < r d i :=
    scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))
  let Kinv := jointBooleanInverseBudget (O := O) (α := α) h C κ
  let Hderiv := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
  have hS : 0 ≤ S := jointBooleanWeightBudget_nonneg h C hC A T r (fun d i => (hr d i).le)
    κ (fun d => (hκ d).le)
  let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
    (degree + 2) (booleanJetMassBudget (Fintype.card α) degree Csum +
      booleanJetMassBudget (Fintype.card α) degree Wsum)
  have hM : 0 ≤ M := polynomialC2BoxBudget_nonneg _ _
    (add_nonneg (booleanJetMassBudget_nonneg _ _ hCsum) (booleanJetMassBudget_nonneg _ _ hWsum))
  let Q := 1 + 2 * (Kinv : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
    ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let t := polynomialPerturbationScale Kinv M Q (ε / 2) (Fintype.card (Σ d, O d))
  have ht := polynomialPerturbationScale_spec Kinv.coe_nonneg hM hQ (half_pos hε) (Fintype.card (Σ d, O d))
  refine ⟨t, ht.1, ht.2.1, rfl, ?_⟩
  intro μ hμ hbox hclow hcup hcsum P hP φ hφ hbound
  have he := random_coefficient_array_joint_comparison c hc z hz sets hsets h hh hcard block hblock
    c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex
    inputIndex hdegree htaildegree hCsum hWsum hwsum η hη Kinv Hderiv
    (jointBooleanInverseBudget_le h C κ) (jointBooleanDerivativeBudget_le h C)
    t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 μ hμ hbox hclow hcup hcsum P hP φ hφ hbound
  calc
    _ ≤ 2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := he
    _ ≤ ε / 2 + ε / 2 := add_le_add (by linarith) ht.2.2.2.2
    _ = ε := by ring

theorem exists_random_coefficient_array_tolerance
    {Ω D K Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, jointBooleanSampler h (c p.1) sets p.2)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, coefficientArraySampler h (c p.1) sets terms weight exponent
            coefficientIndex inputIndex t (z p.1) p.2)) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  obtain ⟨t, hpos, hone, _, herr⟩ := exists_random_coefficient_array_tolerance_with_scale (Y := Y) c hc z hz sets hsets h hh hcard block hblock c₀ C hc₀ hC
    ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex inputIndex
    hdegree htaildegree hCsum hWsum hwsum hε
  exact ⟨t, hpos, hone, herr⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem exists_uniform_boolean_regularization_with_radius {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (hsets : ∀ d, Function.Injective (sets d)) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := O) (α := α) h c₀ C A T ε ∧
      ∀ c : ∀ d, B d → ℝ, (∀ d o, c₀ d ≤ |c d (block d o)|) →
      (∀ d o, |c d (block d o)| ≤ C d) →
      ∀ b : (Σ d, O d) → ℝ, ∀ φ : ((Σ d, O d) → ℝ) → ℝ,
      Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |(∫ x, regularizedImageDensity (jointBooleanSource h)
          (fun a => b+jointBooleanSampler h c sets a) δ x*φ x) -
        mappedTest (jointBooleanSource h) (fun a => b+jointBooleanSampler h c sets a) φ| ≤ ε := by
  let η : D → ℝ := fun _ => ε/(4*((Fintype.card D : ℝ)+1))
  have hη : ∀ d, 0 < η d := fun _ => div_pos hε (by positivity)
  have hsmall : 2*(∑ d, η d) ≤ ε/2 := by
    have hn : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
    have hv : 0 ≤ ε/(4*((Fintype.card D : ℝ)+1)) := (div_pos hε (by positivity)).le
    have he : ((Fintype.card D : ℝ)+1)*(ε/(4*((Fintype.card D : ℝ)+1))) = ε/4 := by
      field_simp
    have hm := mul_le_mul_of_nonneg_right (show (Fintype.card D : ℝ) ≤ (Fintype.card D : ℝ)+1 by linarith) hv
    rw [he] at hm
    simpa only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (show 2*((Fintype.card D : ℝ)*(ε/(4*((Fintype.card D : ℝ)+1)))) ≤ ε/2 by linarith)
  let L := jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T η
  have hp : 0 < min (1 : ℝ) (ε/(2*(1+(L : ℝ)))) := lt_min zero_lt_one (div_pos hε (by positivity))
  let δ : ℝ≥0 := ⟨min 1 (ε/(2*(1+(L : ℝ)))), hp.le⟩
  have hδ : 0 < δ := hp
  have hδ1 : δ ≤ 1 := by
    change min (1 : ℝ) (ε/(2*(1+(L : ℝ)))) ≤ 1
    exact min_le_left _ _
  have hnoise : (L : ℝ)*δ ≤ ε/2 := by
    have hd : (δ : ℝ) ≤ ε/(2*(1+(L : ℝ))) := min_le_right _ _
    have hs := (le_div_iff₀ (show 0 < 2*(1+(L : ℝ)) by positivity)).mp hd
    nlinarith [δ.coe_nonneg]
  refine ⟨δ, hδ, hδ1, rfl, ?_⟩
  intro c hclow hcup b φ hφ hbound
  apply regularizedImageDensity_translate_error (jointBooleanSource h) (jointBooleanSampler h c sets)
    (jointBooleanSampler_contDiff h c sets).continuous.measurable δ hδ _ b φ hφ hbound
  intro f hf hb
  have he := jointBoolean_regularization_choice_error h hh sets hsets hcard block hblock c₀ C hc₀ hC
    c hclow hcup ψ hψ hrange hzero hone A T hLip hTransition η hη δ hδ f hf hb
  exact he.trans (by change 2*(∑ d, η d)+(L : ℝ)*δ ≤ ε; linarith)

theorem exists_uniform_boolean_regularization {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (hsets : ∀ d, Function.Injective (sets d)) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      ∀ c : ∀ d, B d → ℝ, (∀ d o, c₀ d ≤ |c d (block d o)|) →
      (∀ d o, |c d (block d o)| ≤ C d) →
      ∀ b : (Σ d, O d) → ℝ, ∀ φ : ((Σ d, O d) → ℝ) → ℝ,
      Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |(∫ x, regularizedImageDensity (jointBooleanSource h)
          (fun a => b+jointBooleanSampler h c sets a) δ x*φ x) -
        mappedTest (jointBooleanSource h) (fun a => b+jointBooleanSampler h c sets a) φ| ≤ ε := by
  obtain ⟨δ, hpos, hone, _, herr⟩ := exists_uniform_boolean_regularization_with_radius h hh sets hsets hcard block hblock
    c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition hε
  exact ⟨δ, hpos, hone, herr⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_canonical_raw_sampler_tolerance_with_scale
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Csum Wsum ε ∧
      ∀ (Q : Ω → D → ℝ) (scale : Ω → SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ a k, scale a k ≠ 0) →
      (∀ d, Measurable (fun a => constant a d)) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, canonicalRawOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant 0 z p)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, canonicalRawOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant t z p)) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  obtain ⟨t, ht, ht1, heq, hcomp⟩ := exists_random_coefficient_array_tolerance_with_scale (Y := Y) c hc z hz sets hsets h hh hcard
    block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent
    coefficientIndex (canonicalTupleInput extra) hdegree htaildegree hCsum hWsum hwsum hε
  refine ⟨t, ht, ht1, heq, ?_⟩
  intro Q scale constant hQ hscale hconstant μ hμ hbox hclow hcup hcsum P hP φ hφ hbound
  let P' : Ω × ((Σ d, O d) → ℝ) → Y :=
    fun p => P (p.1, booleanConstantJet sets (constant p.1) + p.2)
  have hP' : Measurable P' := constantJet_postprocess_measurable sets constant hconstant P hP
  have he := hcomp μ hμ hbox hclow hcup hcsum P' hP' φ hφ hbound
  rw [canonicalRawOutput_eq h c sets terms weight exponent coefficientIndex extra Q scale constant hQ hscale 0,
    canonicalRawOutput_eq h c sets terms weight exponent coefficientIndex extra Q scale constant hQ hscale t]
  simpa only [coefficientArraySampler_zero, P'] using he

theorem exists_canonical_raw_sampler_tolerance
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ (Q : Ω → D → ℝ) (scale : Ω → SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ a k, scale a k ≠ 0) →
      (∀ d, Measurable (fun a => constant a d)) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, canonicalRawOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant 0 z p)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, canonicalRawOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant t z p)) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  obtain ⟨t, hpos, hone, _, herr⟩ := exists_canonical_raw_sampler_tolerance_with_scale (Y := Y) c hc z hz sets hsets h hh hcard block hblock c₀ C hc₀ hC
    ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex extra
    hdegree htaildegree hCsum hWsum hwsum hε
  exact ⟨t, hpos, hone, herr⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_random_coefficient_smaller_tolerance_with_scale
    {Ω D K Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ) (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Csum Wsum ε ∧
      ∀ s : ℝ, |s| ≤ t →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, jointBooleanSampler h (c p.1) sets p.2)) ∂μ.prod (jointBooleanSource h)) -
          ∫ p, φ (P (p.1, coefficientArraySampler h (c p.1) sets terms weight exponent
            coefficientIndex inputIndex s (z p.1) p.2)) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  obtain ⟨t, ht, ht1, hteq, _⟩ := exists_random_coefficient_array_tolerance_with_scale
    (Y := Y) c hc z hz sets hsets h hh hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone
    A T hLip hTransition terms weight exponent coefficientIndex inputIndex hdegree htaildegree
    hCsum hWsum hwsum hε
  refine ⟨t, ht, ht1, hteq, ?_⟩
  intro s hs
  have hratio : |s / t| ≤ 1 := by
    rw [abs_div, abs_of_pos ht]
    exact (div_le_one ht).mpr hs
  have hw : ∀ d, (∑ n ∈ terms d, |(s / t) * weight d n|) ≤ Wsum :=
    fun d => coefficientTailWeightSum_scale_le (terms d) (weight d) hratio (hwsum d)
  obtain ⟨t', _, _, ht'eq, hcomp⟩ := exists_random_coefficient_array_tolerance_with_scale
    (Y := Y) c hc z hz sets hsets h hh hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone
    A T hLip hTransition terms (fun d n => (s / t) * weight d n) exponent coefficientIndex inputIndex
    hdegree htaildegree hCsum hWsum hw hε
  have hsame : t' = t := ht'eq.trans hteq.symm
  subst t'
  rw [← hteq] at hcomp
  have hcancel : t * (s / t) = s := by field_simp
  intro μ hμ hbox hclow hcup hcsum P hP φ hφ hbound
  simpa only [coefficientArraySampler_scale_weight, hcancel] using
    hcomp μ hμ hbox hclow hcup hcsum P hP φ hφ hbound

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_raw_source_tolerance_with_scale
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanPerturbationScale (B := B) (O := O) (α := α) Z h c₀ C A T degree Csum Wsum ε ∧
      ∀ (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ k, 0 < scale k) →
      (∀ d, Measurable (fun a => constant a d)) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant 0 z p))
              ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) -
          ∫ p, φ (P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant t z p))
              ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))| ≤ ε := by
  obtain ⟨t, ht, ht1, heq, hcomp⟩ := exists_canonical_raw_sampler_tolerance_with_scale (Y := Y) c hc z hz sets hsets h hh hcard
    block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent
    coefficientIndex extra hdegree htaildegree hCsum hWsum hwsum hε
  refine ⟨t, ht, ht1, heq, ?_⟩
  intro Q scale constant hQ hscale hconstant μ hμ hbox hclow hcup hcsum P hP φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  rw [rawSourceOutput_integral h c sets terms weight exponent coefficientIndex extra Q scale constant
      (fun i => hscale (.inr i)) 0 z μ (fun p => φ (P p)),
    rawSourceOutput_integral h c sets terms weight exponent coefficientIndex extra Q scale constant
      (fun i => hscale (.inr i)) t z μ (fun p => φ (P p))]
  exact hcomp Q (fun _ => scale) constant hQ (fun _ k => (hscale k).ne') hconstant
    μ hμ hbox hclow hcup hcsum P hP φ hφ hbound

theorem exists_raw_source_tolerance
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : Ω → D → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ k, 0 < scale k) →
      (∀ d, Measurable (fun a => constant a d)) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
      (∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ Csum) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant 0 z p))
              ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) -
          ∫ p, φ (P (p.1, rawSourceOutput h c sets terms weight exponent coefficientIndex extra
              Q scale constant t z p))
              ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))| ≤ ε := by
  obtain ⟨t, hpos, hone, _, herr⟩ := exists_raw_source_tolerance_with_scale (Y := Y) c hc z hz sets hsets h hh hcard block hblock c₀ C hc₀ hC
    ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex extra
    hdegree htaildegree hCsum hWsum hwsum hε
  exact ⟨t, hpos, hone, herr⟩

end Erdos3

end

end OAI
