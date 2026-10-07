/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Dynamics.PartitionedRegularizationBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

theorem exists_retained_boolean_regularization_with_radius {Ω D α : Type*} [MeasurableSpace Ω]
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
      ∀ (c : Ω → ∀ d, B d → ℝ) (b : Ω → (Σ d, O d) → ℝ),
      (∀ d j, Measurable (fun a => c a d j)) → Measurable b →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, (∀ d o, c₀ d ≤ |c a d (block d o)|) ∧ (∀ d o, |c a d (block d o)| ≤ C d)) →
      ∀ φ : Ω × ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      |(∫ p, regularizedImageDensity (jointBooleanSource h)
          (fun x => b p.1+jointBooleanSampler h (c p.1) sets x) δ p.2*φ p ∂μ.prod volume) -
        ∫ p, φ (p.1, b p.1+jointBooleanSampler h (c p.1) sets p.2) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  obtain ⟨δ, hδ, hδ1, heq, herr⟩ := exists_uniform_boolean_regularization_with_radius h hh sets hsets hcard block hblock
    c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, heq, ?_⟩
  intro c b hc hb μ hμ hgood φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  have hU : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      b p.1+jointBooleanSampler h (c p.1) sets p.2) :=
    (hb.comp measurable_fst).add (jointBooleanSampler_measurable_frozen h sets c hc)
  apply conditionalRegularizedDensity_test_error μ (jointBooleanSource h) _ hU δ hδ _ φ hφ hbound
  filter_upwards [hgood] with a ha
  exact herr (c a) ha.1 ha.2 (b a)

theorem exists_retained_boolean_regularization {Ω D α : Type*} [MeasurableSpace Ω]
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
      ∀ (c : Ω → ∀ d, B d → ℝ) (b : Ω → (Σ d, O d) → ℝ),
      (∀ d j, Measurable (fun a => c a d j)) → Measurable b →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, (∀ d o, c₀ d ≤ |c a d (block d o)|) ∧ (∀ d o, |c a d (block d o)| ≤ C d)) →
      ∀ φ : Ω × ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      |(∫ p, regularizedImageDensity (jointBooleanSource h)
          (fun x => b p.1+jointBooleanSampler h (c p.1) sets x) δ p.2*φ p ∂μ.prod volume) -
        ∫ p, φ (p.1, b p.1+jointBooleanSampler h (c p.1) sets p.2) ∂μ.prod (jointBooleanSource h)| ≤ ε := by
  obtain ⟨δ, hpos, hone, _, herr⟩ := exists_retained_boolean_regularization_with_radius (Ω := Ω) h hh sets hsets hcard block hblock
    c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition hε
  exact ⟨δ, hpos, hone, herr⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem partitioned_coefficient_global_tolerance
    {Ω D G K Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    {L : {d // ¬P d} → Type*}
    (c : Ω → ∀ d : {d // ¬P d}, B d.val → ℝ)
    (hc : ∀ d b, Measurable (fun a => c a d b))
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
    (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d : {d // ¬P d}, O d.val → B d.val)
    (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → K →₀ ℕ)
    (coefficientIndex : ∀ d, L d → PartitionedProfileNoiseIndex G Z α B h P)
    (inputIndex : K → Option α → PartitionedProfileNoiseIndex G Z α B h P ⊕
      PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d))
    {degree : ℕ}
    (htaildegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree)
    {Wsum : ℝ} (hWsum : 0 ≤ Wsum)
    (hwsum : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    let t := booleanMassPerturbationScale (B := B) (O := O) (α := α)
      (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h c₀ C A T degree Wsum ε
    0 < t ∧ t ≤ 1 ∧ ∀ s : ℝ, |s| ≤ t →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d o, c₀ d.val ≤ |c a d (block d o)|) →
      (∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ C d.val) →
      ∀ F : Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → Y, Measurable F →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (F (p.1, jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
              (c p.1) sets p.2)) ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))) -
          ∫ p, φ (F (p.1, coefficientArraySampler (fun d : {d // ¬P d} => h d.val)
            (c p.1) sets terms weight exponent coefficientIndex inputIndex s (z p.1) p.2))
              ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  let η : D → ℝ := fun _ => (ε / 4) / ((Fintype.card D : ℝ) + 1)
  have hη (d : D) : 0 < η d := by dsimp [η]; positivity
  have hsum : (∑ d, η d) ≤ ε / 4 := by
    simp only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hsumP : (∑ d : {d // ¬P d}, η d.val) ≤ ∑ d, η d :=
    nonnegative_axis_sum_restrict_le (fun d => ¬P d) η (fun d => (hη d).le)
  let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
  have hκ (d : D) : 0 < κ d :=
    canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (hη d)
  let r := fun d (_ : B d × Fin (h d)) =>
    scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  have hr (d : D) (i : B d × Fin (h d)) : 0 < r d i :=
    scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))
  let Kinv := jointBooleanInverseBudget (O := O) (α := α) h C κ
  let Hderiv := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
  have hS : 0 ≤ S := jointBooleanWeightBudget_nonneg h C hC A T r
    (fun d i => (hr d i).le) κ (fun d => (hκ d).le)
  let SP := jointBooleanWeightBudget (B := fun d : {d // ¬P d} => B d.val)
    (O := fun d : {d // ¬P d} => O d.val) (α := α)
    (fun d => h d.val) (fun d => C d.val) A T (fun d => r d.val) (fun d => κ d.val)
  have hSP : SP ≤ S := jointBooleanWeightBudget_restrict_le (fun d => ¬P d)
    h C hC A T r (fun d i => (hr d i).le) κ (fun d => (hκ d).le)
  let M := booleanMassToleranceC2 (B := B) (α := α)
    (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h degree Wsum
  have hM : 0 ≤ M := booleanMassToleranceC2_nonneg _ h degree hWsum
  have hMP : polynomialMassC2Budget
      (Fintype.card (PolynomialParameter (PartitionedProfileNoiseIndex G Z α B h P)
        (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d))))
      (degree + 1) (booleanJetMassBudget (Fintype.card α) degree Wsum) = M :=
    partitionedMassToleranceC2_eq h P degree Wsum
  have hdim : (Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α)
      (fun d => ¬P d)) : ℝ) ≤ Fintype.card (JointBlockParameter B h α) := by
    exact_mod_cast dependentAxis_card_restrict_le
      (fun d => BlockParameter (B d) (Fin (h d)) α) (fun d => ¬P d)
  have hout : (Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ) ≤ Fintype.card (Σ d, O d) := by
    exact_mod_cast dependentAxis_card_restrict_le O (fun d => ¬P d)
  let Q := 1 + 2 * (Kinv : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
    ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
  let QP := 1 + 2 * (Kinv : ℝ) * SP +
    (Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d)) : ℝ) *
      ((2 * (Kinv : ℝ)) ^ 2 * ((Hderiv : ℝ) + 1))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hQP : QP ≤ Q := by
    dsimp only [QP, Q]
    gcongr
  let t := polynomialPerturbationScale Kinv M Q (ε / 2) (Fintype.card (Σ d, O d))
  have ht := polynomialPerturbationScale_spec Kinv.coe_nonneg hM hQ (half_pos hε)
    (Fintype.card (Σ d, O d))
  have htpos : 0 < t := ht.1
  change 0 < t ∧ t ≤ 1 ∧ _
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro s hs μ hμ hbox hclow hcup F hF φ hφ hbound
  have hratio : |s / t| ≤ 1 := by
    rw [abs_div, abs_of_pos ht.1]
    exact (div_le_one ht.1).mpr hs
  have hw : ∀ d, (∑ n ∈ terms d, |(s / t) * weight d n|) ≤ Wsum :=
    fun d => coefficientTailWeightSum_scale_le (terms d) (weight d) hratio (hwsum d)
  have hcancel : t * (s / t) = s := by field_simp [ne_of_gt htpos]
  have he := random_coefficient_array_mass_comparison c hc z hz sets hsets
    (fun d : {d // ¬P d} => h d.val) (fun d => hh d.val) hcard block hblock
    (fun d => c₀ d.val) (fun d => C d.val) (fun d => hc₀ d.val) (fun d => hC d.val)
    ψ hψ hrange hzero hone A T hLip hTransition terms (fun d n => (s / t) * weight d n)
    exponent coefficientIndex inputIndex htaildegree hWsum hw (fun d => η d.val)
    (fun d => hη d.val) Kinv Hderiv
    (fun d => jointBooleanInverseBudget_le h C κ d.val)
    (fun d => jointBooleanDerivativeBudget_le h C d.val)
    t ht.1 (by rw [hMP]; exact ht.2.2.1) (by rw [hMP]; exact ht.2.2.2.1)
    μ hμ hbox hclow hcup F hF φ hφ hbound
  have herr : 2 * (∑ d : {d // ¬P d}, η d.val) +
      4 * (Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ) * Real.sqrt (QP * (t * (1 + M))) ≤ ε := by
    calc
      _ ≤ 2 * (∑ d, η d) +
          4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := by
        gcongr
      _ ≤ ε / 2 + ε / 2 := add_le_add (by linarith) ht.2.2.2.2
      _ = ε := by ring
  apply le_trans _ herr
  simpa only [coefficientArraySampler_scale_weight, hcancel, hMP] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem uniform_partition_profile_comparison
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree) {ε : ℝ} (hε : 0 < ε) :
    let t := booleanMassPerturbationScale (B := B) (O := O) (α := α)
      (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h
      (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
      A T degree 1 ε
    0 < t ∧ t ≤ 1 ∧
      ∀ (P : D → Prop) [DecidablePred P],
      ∀ (extra : G → Option α → Z)
        (sets : ∀ d : {d // ¬P d}, O d.val → Finset α),
      (∀ d, Function.Injective (sets d)) → (∀ d o, (sets d o).card ≤ h d.val) →
      ∀ block : ∀ d : {d // ¬P d}, O d.val → B d.val,
      (∀ d, Function.Injective (block d)) →
      ∀ z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
      (∀ j, Measurable (fun a => z a j)) →
      ∀ s : ℝ, |s| ≤ t →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      ∀ R : D → ℝ, ∀ f : Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → ℝ,
      Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      |(∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R 0 (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))) -
        ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R s (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  have hQ := booleanToleranceDivergence_nonneg (B := B) (O := O) (α := α) h hh
    (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
    (unitProfilePrincipalSize_pos (B := B))
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d).le) A T hε
  have hM := booleanMassToleranceC2_nonneg (B := B) (α := α)
    (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h degree zero_le_one
  have ht := polynomialPerturbationScale_spec
    (jointBooleanInverseBudget (O := O) (α := α) h
      (fun d => 2 * unitProfilePrincipalSize (B := B) d)
      (booleanToleranceMinor (O := O) (α := α) h (unitProfilePrincipalSize (B := B)) ε)).coe_nonneg
    hM hQ (half_pos hε) (Fintype.card (Σ d, O d))
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro P instP extra sets hsets hcard block hblock z hz
  let c := fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a => c a d b) := by
    dsimp [c, partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  obtain ⟨_, _, hcomp⟩ := partitioned_coefficient_global_tolerance
    (Y := Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ)) h hh P c hc z hz sets hsets
    hcard block hblock
    (unitProfilePrincipalSize (B := B))
    (fun d => 2 * unitProfilePrincipalSize (B := B) d)
    (unitProfilePrincipalSize_pos (B := B))
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d).le)
    ψ hψ hrange hzero hone A T hLip hTransition
    (partitionedProfileTerms (G := G) (B := B) h P)
    (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
    (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra)
    (fun d e _ => e.property.trans (hdegree d.val))
    (Wsum := 1) zero_le_one (partitionedProfileTail_unit_sum h P) hε
  intro s hs μ hμ hbox R f hf hfb
  have hclow : ∀ᵐ a ∂μ, ∀ d o, unitProfilePrincipalSize (B := B) d.val ≤ |c a d (block d o)| := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).1
  have hcup : ∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ 2 * unitProfilePrincipalSize (B := B) d.val := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).2
  let F : Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) := fun p =>
    (p.1, fun o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z p.1)) o + p.2 o))
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    have hzj := (hz (.inr ⟨o.1.val, constantCoefficientSlot _ _⟩)).comp
      (measurable_fst : Measurable (Prod.fst : Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → Ω))
    dsimp [F, booleanConstantJet, partitionedProfileConstant]
    split_ifs <;> fun_prop
  have hFactual (s : ℝ) (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, coefficientArraySampler (fun d : {d // ¬P d} => h d.val) (c a) sets
        (partitionedProfileTerms (G := G) (B := B) h P)
        (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
        (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra) s (z a) x) =
      (a, partitionedAllocatedProfileJet h P extra sets R s (z a) x) := by
    apply Prod.ext
    · rfl
    dsimp only [F]
    rw [partitionedAllocatedProfileJet_scale]
    unfold partitionedAllocatedProfileJet
    rw [partitionedProfileJet_eq h P extra sets hh]
    rfl
  have hFzero (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, jointBooleanSampler (fun d : {d // ¬P d} => h d.val) (c a) sets x) =
        (a, partitionedAllocatedProfileJet h P extra sets R 0 (z a) x) := by
    simpa only [coefficientArraySampler_zero] using hFactual 0 a x
  simpa only [hFzero, hFactual] using hcomp s hs μ hμ hbox hclow hcup F hF f hf hfb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem exists_uniform_partition_regularization {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := O) (α := α) h c₀ C A T ε ∧
      ∀ (P : D → Prop) [DecidablePred P],
      ∀ sets : ∀ d : {d // ¬P d}, O d.val → Finset α,
      (∀ d, Function.Injective (sets d)) → (∀ d o, (sets d o).card ≤ h d.val) →
      ∀ block : ∀ d : {d // ¬P d}, O d.val → B d.val,
      (∀ d, Function.Injective (block d)) →
      ∀ (c : Ω → ∀ d : {d // ¬P d}, B d.val → ℝ)
        (b : Ω → (Σ d : {d // ¬P d}, O d.val) → ℝ),
      (∀ d j, Measurable (fun a => c a d j)) → Measurable b →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, (∀ d o, c₀ d.val ≤ |c a d (block d o)|) ∧
        (∀ d o, |c a d (block d o)| ≤ C d.val)) →
      ∀ φ : Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → ℝ,
      Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      |(∫ p, regularizedImageDensity (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
          (fun x => b p.1 + jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
            (c p.1) sets x) δ p.2 * φ p ∂μ.prod volume) -
        ∫ p, φ (p.1, b p.1 + jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
          (c p.1) sets p.2) ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  let η : D → ℝ := fun _ => ε / (4 * ((Fintype.card D : ℝ) + 1))
  have hη (d : D) : 0 < η d := by dsimp [η]; positivity
  have hsmall : 2 * (∑ d, η d) ≤ ε / 2 := by
    have hn : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
    have hv : 0 ≤ ε / (4 * ((Fintype.card D : ℝ) + 1)) := by positivity
    have he : ((Fintype.card D : ℝ) + 1) *
        (ε / (4 * ((Fintype.card D : ℝ) + 1))) = ε / 4 := by field_simp
    have hm := mul_le_mul_of_nonneg_right
      (show (Fintype.card D : ℝ) ≤ (Fintype.card D : ℝ) + 1 by linarith) hv
    rw [he] at hm
    simpa only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (show 2 * ((Fintype.card D : ℝ) * (ε / (4 * ((Fintype.card D : ℝ) + 1)))) ≤ ε / 2 by linarith)
  let L := jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T η
  have hspec := regularizationRadius_spec L.coe_nonneg hε
  let δ : ℝ≥0 := ⟨regularizationRadius L ε, hspec.1.le⟩
  have hδ : 0 < δ := hspec.1
  have hδ1 : δ ≤ 1 := hspec.2.1
  have hnoise : (L : ℝ) * δ ≤ ε / 2 := hspec.2.2
  refine ⟨δ, hδ, hδ1, rfl, ?_⟩
  intro P instP sets hsets hcard block hblock c b hc hb μ hμ hgood φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  have hLP : (jointBooleanRegularizationBudget (B := fun d : {d // ¬P d} => B d.val)
      (O := fun d : {d // ¬P d} => O d.val) (α := α)
      (fun d => h d.val) (fun d => c₀ d.val) (fun d => C d.val) A T (fun d => η d.val) : ℝ) ≤ L := by
    exact_mod_cast jointBooleanRegularizationBudget_restrict_le (B := B) (O := O) (α := α)
      (fun d => ¬P d) h hh c₀ C hc₀ hC A T η hη
  have hsumP : (∑ d : {d // ¬P d}, η d.val) ≤ ∑ d, η d :=
    nonnegative_axis_sum_restrict_le (fun d => ¬P d) η (fun d => (hη d).le)
  have hU : Measurable (fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      b p.1 + jointBooleanSampler (fun d : {d // ¬P d} => h d.val) (c p.1) sets p.2) :=
    (hb.comp measurable_fst).add
      (jointBooleanSampler_measurable_frozen (fun d : {d // ¬P d} => h d.val) sets c hc)
  apply conditionalRegularizedDensity_test_error μ
    (jointBooleanSource (fun d : {d // ¬P d} => h d.val)) _ hU δ hδ _ φ hφ hbound
  filter_upwards [hgood] with a ha
  intro f hf hfb
  apply regularizedImageDensity_translate_error
    (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
    (jointBooleanSampler (fun d : {d // ¬P d} => h d.val) (c a) sets)
    (jointBooleanSampler_contDiff (fun d : {d // ¬P d} => h d.val) (c a) sets).continuous.measurable
    δ hδ _ (b a) f hf hfb
  intro g hg hgb
  have he := jointBoolean_regularization_choice_error
    (fun d : {d // ¬P d} => h d.val) (fun d => hh d.val) sets hsets hcard block hblock
    (fun d => c₀ d.val) (fun d => C d.val) (fun d => hc₀ d.val) (fun d => hC d.val)
    (c a) ha.1 ha.2 ψ hψ hrange hzero hone A T hLip hTransition
    (fun d => η d.val) (fun d => hη d.val) δ hδ g hg hgb
  apply he.trans
  have hm := mul_le_mul_of_nonneg_right hLP δ.coe_nonneg
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

theorem exists_uniform_regularized_profile_comparison
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := O) (α := α) h
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B) (O := O) (α := α)
        (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T degree 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ (P : D → Prop) [DecidablePred P],
      ∀ (extra : G → Option α → Z) (sets : ∀ d : {d // ¬P d}, O d.val → Finset α),
      (∀ d, Function.Injective (sets d)) → (∀ d o, (sets d o).card ≤ h d.val) →
      ∀ block : ∀ d : {d // ¬P d}, O d.val → B d.val,
      (∀ d, Function.Injective (block d)) →
      ∀ z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
      (∀ j, Measurable (fun a => z a j)) →
      ∀ s : ℝ, |s| ≤ t → ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      ∀ R : D → ℝ, ∀ f : Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → ℝ,
      Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      |(∫ p, partitionedRegularizedIdeal h P sets δ (z p.1) p.2 *
          f (p.1, fun o => R o.1.val * p.2 o) ∂μ.prod volume) -
        ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R s (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  obtain ⟨δ, hδ, hδ1, hδeq, hreg⟩ := exists_uniform_partition_regularization (Ω := Ω)
    (B := B) (O := O) (α := α) h hh (unitProfilePrincipalSize (B := B))
    (fun d => 2 * unitProfilePrincipalSize (B := B) d)
    (unitProfilePrincipalSize_pos (B := B))
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d).le)
    ψ hψ hrange hzero hone A T hLip hTransition (half_pos hε)
  have ht := uniform_partition_profile_comparison (Ω := Ω) (G := G) (Z := Z) (B := B) (O := O) (α := α)
    h hh ψ hψ hrange hzero hone A T hLip hTransition hdegree (half_pos hε)
  refine ⟨δ, hδ, hδ1, hδeq, ht.1, ht.2.1, ?_⟩
  intro P instP extra sets hsets hcard block hblock z hz s hs μ hμ hbox R f hf hfb
  let c := fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)
  let b := fun a => booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z a))
  have hc (d : {d // ¬P d}) (j : B d.val) : Measurable (fun a => c a d j) := by
    dsimp [c, partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  have hb : Measurable b := by
    apply booleanConstantJet_measurable_comp
    intro d
    dsimp [partitionedProfileConstant]
    exact measurable_const.mul (hz _)
  have hgood : ∀ᵐ a ∂μ,
      (∀ d o, unitProfilePrincipalSize (B := B) d.val ≤ |c a d (block d o)|) ∧
      (∀ d o, |c a d (block d o)| ≤ 2 * unitProfilePrincipalSize (B := B) d.val) := by
    filter_upwards [hbox] with a ha
    exact ⟨fun d o => (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).1,
      fun d o => (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).2⟩
  let scale : Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) →
      Ω × ((Σ d : {d // ¬P d}, O d.val) → ℝ) :=
    fun p => (p.1, fun o => R o.1.val * p.2 o)
  have hscale : Measurable scale := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    exact measurable_const.mul ((measurable_pi_apply o).comp measurable_snd)
  have hreg' := hreg P sets hsets hcard block hblock c b hc hb μ hμ hgood
    (fun p => f (scale p)) (hf.comp hscale) (fun p => hfb (scale p))
  have hzero' (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      scale (a, b a + jointBooleanSampler (fun d : {d // ¬P d} => h d.val) (c a) sets x) =
      (a, partitionedAllocatedProfileJet h P extra sets R 0 (z a) x) := by
    apply Prod.ext
    · rfl
    exact (partitionedAllocatedProfileJet_zero h P sets hh extra R (z a) x).symm
  simp only [hzero'] at hreg'
  have hraw := ht.2.2 P extra sets hsets hcard block hblock z hz s hs μ hμ hbox R f hf hfb
  have htri := abs_sub_le
    (∫ p, partitionedRegularizedIdeal h P sets δ (z p.1) p.2 * f (scale p) ∂μ.prod volume)
    (∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R 0 (z p.1) p.2)
      ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val)))
    (∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R s (z p.1) p.2)
      ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val)))
  apply htri.trans
  change |(∫ p, partitionedRegularizedIdeal h P sets δ (z p.1) p.2 * f (scale p) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R 0 (z p.1) p.2)
        ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε / 2 at hreg'
  linarith

end Erdos3

end

end OAI
