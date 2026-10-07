import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Polynomial.SlicedPolynomialPerturbation

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem product_image_comparison_of_ae_fiber_bounds
    {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F G : Z × X → Y) (hF : Measurable F) (hG : Measurable G)
    {ε : ℝ} (hε : ∀ᵐ z ∂μ, ∀ f : Y → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ x, f (F (z, x)) ∂ν) - ∫ x, f (G (z, x)) ∂ν| ≤ ε)
    (φ : Z × Y → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    |(∫ p, φ (p.1, F p) ∂μ.prod ν) - ∫ p, φ (p.1, G p) ∂μ.prod ν| ≤ ε := by
  have hf : Integrable (fun p : Z × X => φ (p.1, F p)) (μ.prod ν) :=
    mappedTest_integrable _ _ (measurable_fst.prodMk hF) φ hφ hbound
  have hg : Integrable (fun p : Z × X => φ (p.1, G p)) (μ.prod ν) :=
    mappedTest_integrable _ _ (measurable_fst.prodMk hG) φ hφ hbound
  have hb : ∀ᵐ z ∂μ, ‖(∫ x, φ (z, F (z, x)) ∂ν) - ∫ x, φ (z, G (z, x)) ∂ν‖ ≤ ε := by
    filter_upwards [hε] with z hz
    rw [Real.norm_eq_abs]
    exact hz (fun y => φ (z, y)) (hφ.comp (measurable_const.prodMk measurable_id))
      (fun y => hbound (z, y))
  rw [integral_prod _ hf, integral_prod _ hg, ← integral_sub hf.integral_prod_left hg.integral_prod_left]
  have ht := norm_integral_le_of_norm_le (integrable_const ε (μ := μ))
    hb
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul] using ht

theorem product_image_comparison_of_fiber_bounds
    {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F G : Z × X → Y) (hF : Measurable F) (hG : Measurable G)
    {ε : ℝ} (hε : ∀ z, ∀ f : Y → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ x, f (F (z, x)) ∂ν) - ∫ x, f (G (z, x)) ∂ν| ≤ ε)
    (φ : Z × Y → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    |(∫ p, φ (p.1, F p) ∂μ.prod ν) - ∫ p, φ (p.1, G p) ∂μ.prod ν| ≤ ε :=
  product_image_comparison_of_ae_fiber_bounds μ ν F G hF hG (Filter.Eventually.of_forall hε) φ hφ hbound

theorem postprocessed_image_comparison_of_ae_fiber_bounds
    {Z X Y W : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (μ : Measure Z) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F G : Z × X → Y) (hF : Measurable F) (hG : Measurable G)
    {ε : ℝ} (hε : ∀ᵐ z ∂μ, ∀ f : Y → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ x, f (F (z, x)) ∂ν) - ∫ x, f (G (z, x)) ∂ν| ≤ ε)
    (H : Z × Y → W) (hH : Measurable H)
    (φ : W → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    |(∫ p, φ (H (p.1, F p)) ∂μ.prod ν) - ∫ p, φ (H (p.1, G p)) ∂μ.prod ν| ≤ ε :=
  product_image_comparison_of_ae_fiber_bounds μ ν F G hF hG hε
    (fun p => φ (H p)) (hφ.comp hH) (fun p => hbound (H p))

theorem retained_image_comparison_of_fiber_bounds
    {Z X Y W : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (μ : Measure Z) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F G : Z × X → Y) (hF : Measurable F) (hG : Measurable G)
    (grid : Z → W) (hgrid : Measurable grid)
    {ε : ℝ} (hε : ∀ z, ∀ f : Y → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ x, f (F (z, x)) ∂ν) - ∫ x, f (G (z, x)) ∂ν| ≤ ε)
    (φ : W × Y → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    |(∫ p, φ (grid p.1, F p) ∂μ.prod ν) - ∫ p, φ (grid p.1, G p) ∂μ.prod ν| ≤ ε :=
  product_image_comparison_of_fiber_bounds μ ν F G hF hG hε
    (fun p => φ (grid p.1, p.2)) (hφ.comp ((hgrid.comp measurable_fst).prodMk measurable_snd))
    (fun p => hbound (grid p.1, p.2))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem coefficientArraySampler_mass_c2_error
    {D K Z α : Type*} [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z]
    [Fintype α] [DecidableEq α] {B O T : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {H : ℕ} (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ W)
    (t : ℝ) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (x : JointBlockParameter B h α → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    let V := coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z
    let U := jointBooleanSampler h c sets
    let M := polynomialMassC2Budget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
      (H + 1) (booleanJetMassBudget (Fintype.card α) H W)
    ‖V x - U x‖ ≤ |t| * M ∧
      ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ |t| * M ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ |t| * M := by
  let r := jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex
  have hrdeg : ∀ o i, (r o).degreeOf i ≤ H + 1 := fun o i =>
    (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      (jointCoefficientTail_degree h sets terms weight exponent coefficientIndex inputIndex hdegree o)
  have hrmass : ∀ o, realPolynomialMass (r o) ≤ booleanJetMassBudget (Fintype.card α) H W :=
    jointCoefficientTail_mass h sets terms weight exponent coefficientIndex inputIndex hdegree hw
  have hb := parameterPolynomialMap_mass_c2_bounds r hrdeg (booleanJetMassBudget_nonneg _ _ hW)
    hrmass (t := 0) (by norm_num) z hz x hx
  have hV : coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z =
      parameterPolynomialMap (jointBooleanPerturbedPolynomial h c sets r) t z := by
    exact coefficientArraySampler_polynomial h c sets terms weight exponent coefficientIndex inputIndex t z
  apply factoredDifference_c2_bounds _ _ (parameterPolynomialMap r 0 z) t
    (by rw [hV]; exact (parameterPolynomialMap_contDiff _ _ _).of_le (by norm_num))
    ((jointBooleanSampler_contDiff h c sets).of_le (by norm_num))
    ((parameterPolynomialMap_contDiff r 0 z).of_le (by norm_num)) _ x hb.1 hb.2.1 hb.2.2
  intro y
  funext o
  change jointBooleanSampler h c sets y o + t * normalizedCoefficientTailValue _ _ _ _ _ z y _ -
    jointBooleanSampler h c sets y o = t * MvPolynomial.eval (polynomialParameterPoint 0 z y) (r o)
  simp only [r, jointCoefficientTail, normalizedCoefficientTail_eval, add_sub_cancel_left]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem coefficient_array_mass_comparison
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
    {degree : ℕ} (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Wsum : ℝ} (hWsum : 0 ≤ Wsum) (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) :
    ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
      let M := polynomialMassC2Budget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
        (degree + 1) (booleanJetMassBudget (Fintype.card α) degree Wsum)
      ∀ Kinv Hderiv : ℝ≥0,
      (∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 (κ d) ≤ Kinv) →
      (∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ Hderiv) →
      ∀ t : ℝ, 0 < t → (Kinv : ℝ) * (t * M) ≤ 1 / 2 → t * M ≤ 1 →
      ∀ z : Z → ℝ, (∀ j, |z j| ≤ 1) →
      ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        let Q := 1 + 2 * (Kinv : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
          ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
        |(∫ x, φ (jointBooleanSampler h c sets x) ∂jointBooleanSource h) -
          ∫ x, φ (coefficientArraySampler h c sets terms weight exponent
            coefficientIndex inputIndex t z x) ∂jointBooleanSource h| ≤
          2 * (∑ d, η d) + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := by
  obtain ⟨sel, hsel⟩ := exists_joint_boolean_good_region c sets hsets h hh hcard block hblock
    c₀ hc₀ hclow ψ hψ hrange hzero hone
  intro η hη
  dsimp only
  intro Kinv Hderiv hK hH t ht hsmall hsecond z hz φ hφ hbound
  obtain ⟨hκ, _, _, _, hmass, _, _⟩ := hsel η hη
  apply jointBoolean_c2_comparison c sets block hblock (fun d => ⟨0, hh d⟩) sel hcard C hC hcup
    ψ hψ hrange hzero A T hLip hTransition _
    (fun d _ => scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d)))
    _ (fun d => (hκ d).1) Kinv Hderiv hK hH
    (coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z)
    (by rw [coefficientArraySampler_polynomial]; exact (parameterPolynomialMap_contDiff _ _ _).of_le (by norm_num))
    (polynomialMassC2Budget_nonneg _ _ (booleanJetMassBudget_nonneg _ _ hWsum)) ht
    ?_ hsmall hsecond hmass φ hφ hbound
  intro x hx
  have he := coefficientArraySampler_mass_c2_error h c sets terms weight exponent coefficientIndex inputIndex
    htaildegree hWsum hwsum t z hz x hx
  simpa only [abs_of_pos ht] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem random_coefficient_array_mass_comparison
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
    {degree : ℕ}
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Wsum : ℝ} (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) :
    ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
      let M := polynomialMassC2Budget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
        (degree + 1) (booleanJetMassBudget (Fintype.card α) degree Wsum)
      ∀ Kinv Hderiv : ℝ≥0,
      (∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
        (h d) (C d) 1 (κ d) ≤ Kinv) →
      (∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ Hderiv) →
      ∀ t : ℝ, 0 < t → (Kinv : ℝ) * (t * M) ≤ 1 / 2 → t * M ≤ 1 →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d) →
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
  intro Kinv Hderiv hK hH t ht hsmall hsecond μ hμ hbox hclow hcup P hP φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  have hU : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      jointBooleanSampler h (c p.1) sets p.2) :=
    jointBooleanSampler_measurable_frozen h sets c hc
  have hV : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h (c p.1) sets terms weight exponent coefficientIndex inputIndex t
        (z p.1) p.2) :=
    coefficientArraySampler_measurable_frozen h sets terms weight exponent coefficientIndex inputIndex t c hc z hz
  apply postprocessed_image_comparison_of_ae_fiber_bounds μ (jointBooleanSource h) _ _ hU hV ?_ P hP φ hφ hbound
  filter_upwards [hbox, hclow, hcup] with a ha hlowa hupa
  intro f hf hfb
  exact coefficient_array_mass_comparison (c a) sets hsets h hh hcard block hblock c₀ C hc₀ hC
    hlowa hupa ψ hψ hrange hzero hone A T hLip hTransition terms weight exponent coefficientIndex
    inputIndex htaildegree hWsum hwsum η hη Kinv Hderiv hK hH t ht
    hsmall hsecond (z a) ha f hf hfb

end Erdos3

end

end OAI
