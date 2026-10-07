import OAI.Combinatorics.Progressions.Polynomial.JointAffinePolynomialSource

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z K₀ : Type*} [Fintype Z] [DecidableEq Z]
  [fintypeD : Fintype D] [decidableEqD : DecidableEq D] [Fintype α]
  [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [fintypeO : ∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)]
  [nonemptyO : ∀ d, Nonempty (O d)]

omit fintypeD decidableEqD fintypeO decidableEqB decidableEqO nonemptyO in
theorem jointAffineBooleanSampler_coordinateScale
    [Fintype D] [DecidableEq D] [∀ d, Fintype (O d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hw : ∀ d i, width d i ≠ 0) :
    jointAffineBooleanSampler c sets
      (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv) center =
      fun x => jointBooleanSampler h c sets (fun s => center s.1 s.2 + width s.1 s.2 * x s) := rfl

omit fintypeD decidableEqD decidableEqAlpha decidableEqB in
theorem sigmaAxisOperator_coordinateScale
    [Fintype D] [DecidableEq D] [DecidableEq α] [∀ d, DecidableEq (B d)] {h : D → ℕ}
    (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hw : ∀ d i, width d i ≠ 0) :
    (fun x : JointBlockParameter B h α → ℝ => (fun s => center s.1 s.2) +
      sigmaAxisOperator (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap) x) =
      (fun x s => center s.1 s.2 + width s.1 s.2 * x s) := rfl

noncomputable def jointAffineCoefficientTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (degree : ℕ) (Csum Wsum δ E : ℝ) : ℝ :=
  jointAffinePolynomialTolerance (Z := Z) (B := B) (O := O) (α := α) h c₀ C A T
    (degree + 2) (booleanJetMassBudget (Fintype.card α) degree Csum +
      booleanJetMassBudget (Fintype.card α) degree Wsum) δ E

theorem exists_uniform_sliced_coefficient_array_source_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (Csum Wsum : ℝ) (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffineCoefficientTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Csum Wsum δ E ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) → (∀ d, (∑ b, |c d b|) ≤ Csum) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (Terms : D → Type*) (terms : ∀ d, Finset (Terms d)) (weight : ∀ d, Terms d → ℝ)
      (exponent : ∀ d, Terms d → K₀ →₀ ℕ) (coefficientIndex : ∀ d, Terms d → Z)
      (inputIndex : K₀ → Option α → Z ⊕ JointBlockParameter B h α),
    (∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree) →
    (∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) →
    ∀ z : Z → ℝ, (∀ i, |z i| ≤ 1) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z ∘ slice) φ| ≤ E := by
  let Cp := booleanJetMassBudget (Fintype.card α) degree Csum +
    booleanJetMassBudget (Fintype.card α) degree Wsum
  have hCp : 0 ≤ Cp := add_nonneg (booleanJetMassBudget_nonneg _ _ hCsum)
    (booleanJetMassBudget_nonneg _ _ hWsum)
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_uniform_joint_affine_polynomial_source_with_scales (Z := Z)
    h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
    (degree + 2) Cp hCp δ hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro c hclow hcup hcsum center width hw hwidth hbox
  have hd := hs c hclow hcup center width hw hwidth hbox
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_⟩
  intro Terms terms weight exponent coefficientIndex inputIndex hdeg hweight z hz φ hφ hbound
  have hp := coefficientArraySampler_polynomial_bounds h c sets terms weight exponent coefficientIndex
    inputIndex hdegree hdeg hcsum hweight
  rw [coefficientArraySampler_polynomial]
  exact hd.2.2.2.2 _ hp.1 hp.2 z hz (jointBooleanPerturbedPolynomial_zero _ _ _ _ _) φ hφ hbound

theorem exists_uniform_sliced_coefficient_array_source
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (Csum Wsum : ℝ) (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) → (∀ d, (∑ b, |c d b|) ≤ Csum) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (Terms : D → Type*) (terms : ∀ d, Finset (Terms d)) (weight : ∀ d, Terms d → ℝ)
      (exponent : ∀ d, Terms d → K₀ →₀ ℕ) (coefficientIndex : ∀ d, Terms d → Z)
      (inputIndex : K₀ → Option α → Z ⊕ JointBlockParameter B h α),
    (∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree) →
    (∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) →
    ∀ z : Z → ℝ, (∀ i, |z i| ≤ 1) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z ∘ slice) φ| ≤ E := by
  obtain ⟨ρ, hρ, hρone, _, t, ht, htone, _, hs⟩ :=
    exists_uniform_sliced_coefficient_array_source_with_scales (Z := Z) (K₀ := K₀)
      h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
      degree hdegree Csum Wsum hCsum hWsum δ hδ hδone hE
  exact ⟨ρ, hρ, hρone, t, ht, htone, hs⟩

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {Ω D α Z K₀ : Type*} [MeasurableSpace Ω] [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem exists_retained_sliced_coefficient_source_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (Csum Wsum : ℝ) (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffineCoefficientTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Csum Wsum δ E ∧
    ∀ (Terms : D → Type*) (terms : ∀ d, Finset (Terms d)) (weight : ∀ d, Terms d → ℝ)
      (exponent : ∀ d, Terms d → K₀ →₀ ℕ) (coefficientIndex : ∀ d, Terms d → Z)
      (inputIndex : K₀ → Option α → Z ⊕ JointBlockParameter B h α),
    (∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree) →
    (∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) →
    ∀ (c : Ω → ∀ d, B d → ℝ) (center width : Ω → JointBlockParameter B h α → ℝ)
      (z : Ω → Z → ℝ),
    (∀ d b, Measurable (fun a => c a d b)) →
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    (∀ i, Measurable (fun a => z a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ d o, c₀ d ≤ |c a d (block d o)|) ∧
      (∀ d o, |c a d (block d o)| ≤ C d) ∧ (∀ d, (∑ b, |c a d b|) ≤ Csum) ∧
      (∀ i, δ ≤ |width a i|) ∧ (∀ i, |center a i| + |width a i| ≤ 1) ∧
      (∀ i, |z a i| ≤ 1)) →
    let slice := fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      fun i => center p.1 i + width p.1 i * p.2 i
    let U := fun p : Ω × (JointBlockParameter B h α → ℝ) => jointBooleanSampler h (c p.1) sets (slice p)
    let V := fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h (c p.1) sets terms weight exponent coefficientIndex inputIndex t (z p.1) (slice p)
    ∀ φ : Ω × ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ p, regularizedImageDensity (jointBooleanSource (B := B) (α := α) h) (fun x => U (p.1, x)) ρ p.2 * φ p
          ∂μ.prod volume) - ∫ p, φ (p.1, V p) ∂μ.prod (jointBooleanSource (B := B) (α := α) h)| ≤ E := by
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_uniform_sliced_coefficient_array_source_with_scales (Z := Z) (K₀ := K₀)
    h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
    degree hdegree Csum Wsum hCsum hWsum δ hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro Terms terms weight exponent coefficientIndex inputIndex hdeg hweight c center width z hc hb hw hz μ hμ
    hgood slice U V φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  have hx (i) : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) => slice p i) :=
    ((hb i).comp measurable_fst).add (((hw i).comp measurable_fst).mul
      ((measurable_pi_apply i).comp measurable_snd))
  have hU : Measurable U := jointBooleanSampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ)) h sets (fun p => c p.1)
    (fun d b => (hc d b).comp measurable_fst) slice hx
  have hV : Measurable V := coefficientArraySampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ)) h sets terms weight exponent
    coefficientIndex inputIndex t (fun p => c p.1) (fun d b => (hc d b).comp measurable_fst)
    (fun p => z p.1) (fun i => (hz i).comp measurable_fst) slice hx
  apply conditionalRegularizedDensity_comparison μ (jointBooleanSource (B := B) (α := α) h) U V hU hV ρ hρ _ φ hφ hbound
  filter_upwards [hgood] with a ha
  let wa := fun d (i : BlockParameter (B d) (Fin (h d)) α) => width a ⟨d, i⟩
  have hwa (d) (i : BlockParameter (B d) (Fin (h d)) α) : wa d i ≠ 0 :=
    abs_pos.mp (hδ.trans_le (ha.2.2.2.1 ⟨d, i⟩))
  have hd := hs (c a) ha.1 ha.2.1 ha.2.2.1
    (fun d i => center a ⟨d, i⟩) wa hwa
    (fun d i => ha.2.2.2.1 ⟨d, i⟩) (fun d i => ha.2.2.2.2.1 ⟨d, i⟩)
  intro f hf hboundf
  have he := hd.2.2.2.2 Terms terms weight exponent coefficientIndex inputIndex hdeg hweight
    (z a) ha.2.2.2.2.2 f hf hboundf
  dsimp only at he
  rw [jointAffineBooleanSampler_coordinateScale,
    sigmaAxisOperator_coordinateScale (fun d i => center a ⟨d, i⟩) wa hwa] at he
  exact he

theorem exists_retained_sliced_coefficient_source
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (Csum Wsum : ℝ) (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    ∀ (Terms : D → Type*) (terms : ∀ d, Finset (Terms d)) (weight : ∀ d, Terms d → ℝ)
      (exponent : ∀ d, Terms d → K₀ →₀ ℕ) (coefficientIndex : ∀ d, Terms d → Z)
      (inputIndex : K₀ → Option α → Z ⊕ JointBlockParameter B h α),
    (∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree) →
    (∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) →
    ∀ (c : Ω → ∀ d, B d → ℝ) (center width : Ω → JointBlockParameter B h α → ℝ)
      (z : Ω → Z → ℝ),
    (∀ d b, Measurable (fun a => c a d b)) →
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    (∀ i, Measurable (fun a => z a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ d o, c₀ d ≤ |c a d (block d o)|) ∧
      (∀ d o, |c a d (block d o)| ≤ C d) ∧ (∀ d, (∑ b, |c a d b|) ≤ Csum) ∧
      (∀ i, δ ≤ |width a i|) ∧ (∀ i, |center a i| + |width a i| ≤ 1) ∧
      (∀ i, |z a i| ≤ 1)) →
    let slice := fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      fun i => center p.1 i + width p.1 i * p.2 i
    let U := fun p : Ω × (JointBlockParameter B h α → ℝ) => jointBooleanSampler h (c p.1) sets (slice p)
    let V := fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h (c p.1) sets terms weight exponent coefficientIndex inputIndex t (z p.1) (slice p)
    ∀ φ : Ω × ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ p, regularizedImageDensity (jointBooleanSource (B := B) (α := α) h) (fun x => U (p.1, x)) ρ p.2 * φ p
          ∂μ.prod volume) - ∫ p, φ (p.1, V p) ∂μ.prod (jointBooleanSource (B := B) (α := α) h)| ≤ E := by
  obtain ⟨ρ, hρ, hρone, _, t, ht, htone, _, hs⟩ :=
    exists_retained_sliced_coefficient_source_with_scales (Ω := Ω) (Z := Z) (K₀ := K₀)
      h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
      degree hdegree Csum Wsum hCsum hWsum δ hδ hδone hE
  exact ⟨ρ, hρ, hρone, t, ht, htone, hs⟩

end Erdos3

end

end OAI
