/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
  (sets : ∀ d, O d → Finset α)

noncomputable def partitionedSlicedRegularizedIdeal
    (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) : ((Σ d, O d) → ℝ) → ℝ :=
  regularizedImageDensity (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
    (fun x => partitionedIdealMap h P sets z (fun i => center i + width i * x i)) ρ

theorem partitionedSlicedIdealMap_measurable {Ω : Type*} [MeasurableSpace Ω]
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hb : ∀ i, Measurable (fun a => center a i)) (hw : ∀ i, Measurable (fun a => width a i)) :
    Measurable (fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      partitionedIdealMap h P sets (z p.1) (fun i => center p.1 i + width p.1 i * p.2 i)) := by
  let _ : Fintype D := inferInstance
  let _ : Fintype G := inferInstance
  let _ : Fintype Z := inferInstance
  let _ : DecidablePred P := inferInstance
  let _ : ∀ index, Fintype (O index) := inferInstance
  have hi : Measurable (fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      (p.1, fun i => center p.1 i + width p.1 i * p.2 i)) :=
    measurable_fst.prodMk (Measurable.of_eval (fun i =>
      ((hb i).comp measurable_fst).add (((hw i).comp measurable_fst).mul
        ((measurable_pi_apply i).comp measurable_snd))))
  exact (partitionedIdealMap_measurable h P sets z hz).comp
    (f := fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      (p.1, fun i => center p.1 i + width p.1 i * p.2 i)) hi

theorem partitionedSlicedRegularizedIdeal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (ρ : ℝ≥0) (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hb : ∀ i, Measurable (fun a => center a i)) (hw : ∀ i, Measurable (fun a => width a i)) :
    Measurable (fun p : Ω × ((Σ d, O d) → ℝ) =>
      partitionedSlicedRegularizedIdeal h P sets ρ (center p.1) (width p.1) (z p.1) p.2) :=
  conditionalRegularizedDensity_measurable _ _
    (partitionedSlicedIdealMap_measurable h P sets z hz center width hb hw) ρ

theorem partitionedSlicedIdealMap_measurable_fixed
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    Measurable (fun x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ => partitionedIdealMap h P sets z (fun i => center i + width i * x i)) := by
  have hm := partitionedSlicedIdealMap_measurable (Ω := Unit) h P sets (fun _ => z)
    (fun _ => measurable_const) (fun _ => center) (fun _ => width)
    (fun _ => measurable_const) (fun _ => measurable_const)
  exact hm.comp (f := fun x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ => ((), x))
    (measurable_const.prodMk measurable_id)

theorem partitionedSlicedRegularizedIdeal_probability (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    (∀ x, 0 ≤ partitionedSlicedRegularizedIdeal h P sets ρ center width z x) ∧
    Integrable (partitionedSlicedRegularizedIdeal h P sets ρ center width z) ∧
    (∫ x, partitionedSlicedRegularizedIdeal h P sets ρ center width z x) = 1 := by
  apply regularizedImageDensity_probability _ _ _ ρ hρ
  exact partitionedSlicedIdealMap_measurable_fixed h P sets center width z

theorem partitionedSlicedRegularizedIdeal_bounds (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    (∀ x, partitionedSlicedRegularizedIdeal h P sets ρ center width z x ∈
      Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    LipschitzWith (affineProductProfileLip (Σ d, O d) ρ)
      (partitionedSlicedRegularizedIdeal h P sets ρ center width z) := by
  apply regularizedImageDensity_bounds _ _ _ ρ hρ
  exact partitionedSlicedIdealMap_measurable_fixed h P sets center width z

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G : Type*} [Fintype D] [Fintype G]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop)

noncomputable def activeTailRescale (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ)
    (j : ActiveProfileCoefficientIndex G B h P) : ℝ :=
  nonprincipalDilation Subtype.val (canonicalPrincipalExponent h j.1.val) (τ j.1.val) j.2 * r j

theorem activeTailRescale_principal (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (d : {d // ¬P d}) (b : B d.val) :
    activeTailRescale h P τ r ⟨d, principalCoefficientSlot h d.val b⟩ =
      r ⟨d, principalCoefficientSlot h d.val b⟩ := by
  unfold activeTailRescale
  rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d.val)
    (τ d.val) _ b rfl, one_mul]

theorem activeTailRescale_constant (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (d : {d // ¬P d}) :
    activeTailRescale h P τ r ⟨d, constantCoefficientSlot _ _⟩ =
      r ⟨d, constantCoefficientSlot _ _⟩ := by
  unfold activeTailRescale
  rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d.val)
    (τ d.val) _ rfl, one_mul]

theorem activeTailRescale_abs_le (τ : D → ℝ) (hτ : ∀ d, |τ d| ≤ 1)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (hr : ∀ j, |r j| ≤ 1)
    (j : ActiveProfileCoefficientIndex G B h P) : |activeTailRescale h P τ r j| ≤ 1 := by
  have hd : |nonprincipalDilation Subtype.val (canonicalPrincipalExponent h j.1.val)
      (τ j.1.val) j.2| ≤ 1 := by
    unfold nonprincipalDilation
    split_ifs
    · exact hτ _
    · norm_num
  unfold activeTailRescale
  rw [abs_mul]
  exact (mul_le_mul hd (hr j) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem activeTailRescale_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (τ : D → ℝ) (r : Ω → ActiveProfileCoefficientIndex G B h P → ℝ)
    (hr : ∀ j, Measurable (fun a => r a j)) (j : ActiveProfileCoefficientIndex G B h P) :
    Measurable (fun a => activeTailRescale h P τ (r a) j) :=
  measurable_const.mul (hr j)

theorem partitionedIdealMap_activeTailRescale {Z α : Type*}
    [Fintype α] [DecidableEq α] [DecidablePred P]
    {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)
    (τ : D → ℝ) (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedIdealMap h P sets (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      partitionedIdealMap h P sets (profileNoiseWithActive h P z r) := by
  have hc : partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B))
      (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (profileNoiseWithActive h P z r) := by
    funext d b
    simp only [partitionedProfilePrincipal, profileNoiseWithActive_active, activeTailRescale_principal]
  have hb : partitionedProfileConstant h P (fun _ => 1 / 4)
      (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      partitionedProfileConstant h P (fun _ => 1 / 4) (profileNoiseWithActive h P z r) := by
    funext d
    simp only [partitionedProfileConstant, profileNoiseWithActive_active, activeTailRescale_constant]
  unfold partitionedIdealMap
  rw [hc, hb]

theorem partitionedRegularizedIdeal_activeTailRescale {Z α : Type*}
    [Fintype α] [DecidableEq α] [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    (δ : ℝ≥0) (τ : D → ℝ) (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedRegularizedIdeal h P sets δ (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      activeProfileIdeal Z h P sets δ r := by
  unfold activeProfileIdeal partitionedRegularizedIdeal
  rw [partitionedIdealMap_activeTailRescale, partitionedIdealMap_withActive_eq]

theorem boundedProfileWidth_noise_rescale (d : D) (ρ γ ε σ t v : ℝ) (ht : t ≠ 0)
    (e : SamplerCoefficientSlot G B h d) :
    coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (t * ε) e * (nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) (σ / t) e * v) =
      coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (σ * ε) e * v := by
  classical
  by_cases hz : e = constantCoefficientSlot _ _
  · rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d)
      (σ / t) e (congrArg Subtype.val hz)]
    simp only [coefficientProfileWidth, hz, ite_true, one_mul]
  · by_cases hp : e ∈ principalCoefficientSlots h d
    · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
      rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
        (σ / t) e b (congrArg Subtype.val hb.symm)]
      simp only [coefficientProfileWidth, hz, hp, ite_false, ite_true, one_mul]
    · rw [nonprincipalDilation_mem Subtype.val (canonicalPrincipalExponent h d) (σ / t) e
        ((bounded_mem_nonprincipalCoefficientSlots h d e).mpr ⟨hz, hp⟩)]
      simp only [coefficientProfileWidth, hz, hp, ite_false]
      field_simp [ht]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

noncomputable def activeSlicedProfileIdeal (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) : ((Σ d, O d) → ℝ) → ℝ :=
  partitionedSlicedRegularizedIdeal h P sets ρ center width
    (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)

theorem activeSlicedProfileIdeal_measurable (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    Measurable (Function.uncurry (activeSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width)) := by
  apply partitionedSlicedRegularizedIdeal_measurable h P sets ρ _ _
    (fun _ => center) (fun _ => width) (fun _ => measurable_const) (fun _ => measurable_const)
  intro j
  exact profileNoiseWithActive_measurable h P (fun _ _ => 0) id
    (fun _ => measurable_const) (fun i => measurable_pi_apply i) j

noncomputable def activeAveragedSlicedProfileIdeal (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    ((Σ d, O d) → ℝ) → ℝ :=
  densityMixture (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))
    (activeSlicedProfileIdeal Z h P sets ρ center width)

theorem activeAveragedSlicedProfileIdeal_spec (ρ : ℝ≥0) (hρ : 0 < ρ)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (∀ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width v ∈
      Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    LipschitzWith (affineProductProfileLip (Σ d, O d) ρ)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width) ∧
    Integrable (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width) ∧
    (∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width v) = 1 := by
  have hm := activeSlicedProfileIdeal_measurable (G := G) (B := B) Z h P sets ρ center width
  have hb := densityMixture_uniform_bound (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))
    (activeSlicedProfileIdeal Z h P sets ρ center width) (ρ⁻¹ ^ Fintype.card (Σ d, O d))
    (affineProductProfileLip (Σ d, O d) ρ)
    (fun v => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun r => partitionedSlicedRegularizedIdeal_bounds h P sets ρ hρ center width
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)))
  have hp := densityMixture_probability_density
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeSlicedProfileIdeal Z h P sets ρ center width) hm
    (Filter.Eventually.of_forall (fun r => partitionedSlicedRegularizedIdeal_probability h P sets ρ hρ center width
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)))
  exact ⟨hb.1, hb.2, hp.2.1, hp.2.2⟩

theorem partitionedSlicedRegularizedIdeal_activeTailRescale (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (τ : D → ℝ) (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedSlicedRegularizedIdeal h P sets ρ center width
        (profileNoiseWithActive h P z (activeTailRescale h P τ r)) =
      activeSlicedProfileIdeal Z h P sets ρ center width r := by
  let _ : Fintype Z := inferInstance
  unfold activeSlicedProfileIdeal partitionedSlicedRegularizedIdeal
  rw [partitionedIdealMap_activeTailRescale, partitionedIdealMap_withActive_eq]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

noncomputable def activeTailProfileSample {W D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α) (R : D → ℝ) (s : ℝ) (τ : D → ℝ)
    (z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)) :
    W × ((Σ d, O d) → ℝ) :=
  (p.1.1, partitionedAllocatedProfileJet h P extra sets R s
    (profileNoiseWithActive h P (z p.1.1) (activeTailRescale h P τ p.1.2)) p.2)

theorem exists_active_tail_profile_comparison
    {W D G Z α : Type*} [MeasurableSpace W]
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
      ∀ τ : D → ℝ, (∀ d, |τ d| ≤ 1) →
      ∀ z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
      (∀ j, Measurable (fun a => z a j)) →
      ∀ s : ℝ, |s| ≤ t → ∀ μ : Measure W, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      ∀ R : D → ℝ, ∀ f : W × ((Σ d : {d // ¬P d}, O d.val) → ℝ) → ℝ,
      Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      |(∫ p, activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ p.2 *
          f (p.1, fun o => R o.1.val * p.2 o) ∂μ.prod volume) -
        ∫ p, f (activeTailProfileSample h P extra sets R s τ z p)
          ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
            (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, _⟩ := exists_uniform_regularized_profile_comparison
    (Ω := W) (G := G) (Z := Z) (B := B) (O := O) (α := α)
    h hh ψ hψ hrange hzero hone A T hLip hTransition hdegree hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro P instP extra sets hsets hcard block hblock τ hτ z hz s hs μ hμ hbox R f hf hfb
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨δ', _, _, hδ'eq, _, _, hcomp⟩ := exists_uniform_regularized_profile_comparison
    (Ω := W × (ActiveProfileCoefficientIndex G B h P → ℝ))
    (G := G) (Z := Z) (B := B) (O := O) (α := α)
    h hh ψ hψ hrange hzero hone A T hLip hTransition hdegree hε
  have hsame : δ' = δ := NNReal.coe_injective (hδ'eq.trans hδeq.symm)
  subst δ'
  let ζ := fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) =>
    profileNoiseWithActive h P (z p.1) (activeTailRescale h P τ p.2)
  have hζ (j : PartitionedProfileNoiseIndex G Z α B h P) : Measurable (fun p => ζ p j) :=
    profileNoiseWithActive_measurable h P
      (fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) => z p.1)
      (fun p => activeTailRescale h P τ p.2)
      (fun i => (hz i).comp measurable_fst)
      (activeTailRescale_measurable_comp h P τ Prod.snd
        (fun i => (measurable_pi_apply i).comp measurable_snd)) j
  have hζbox : ∀ᵐ p ∂μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)),
      ∀ j, |ζ p j| ≤ 1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbox,
      Measure.quasiMeasurePreserving_snd.ae
        (unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P))] with p hp hr
    exact profileNoiseWithActive_abs_le h P (z p.1) (activeTailRescale h P τ p.2) hp
      (activeTailRescale_abs_le h P τ hτ p.2 hr)
  let f' := fun p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      ((Σ d : {d // ¬P d}, O d.val) → ℝ) => f (p.1.1, p.2)
  have hf' : Measurable f' := hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have he := hcomp P extra sets hsets hcard block hblock ζ hζ s hs
    (μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))) inferInstance
    hζbox R f' hf' (fun p => hfb (p.1.1, p.2))
  simp only [ζ, partitionedRegularizedIdeal_activeTailRescale] at he
  let Φ := fun p : W × ((Σ d : {d // ¬P d}, O d.val) → ℝ) =>
    f (p.1, fun o => R o.1.val * p.2 o)
  have hΦ : Measurable Φ := by
    apply hf.comp
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    exact measurable_const.mul ((measurable_pi_apply o).comp measurable_snd)
  have havg := retained_coefficient_density_average μ
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeProfileIdeal Z h P sets δ) (activeProfileIdeal_measurable Z h P sets δ)
    (fun r => partitionedRegularizedIdeal_probability h P sets δ hδ
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)) Φ hΦ
    (fun p => hfb (p.1, fun o => R o.1.val * p.2 o))
  change |(∫ p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      ((Σ d : {d // ¬P d}, O d.val) → ℝ),
      activeProfileIdeal Z h P sets δ p.1.2 p.2 * Φ (p.1.1, p.2)
      ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod volume) -
      ∫ p, f (activeTailProfileSample h P extra sets R s τ z p)
        ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
          (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε at he
  rw [havg] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z]
  [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
  (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)

noncomputable def activeAveragedSlicedIdealSiteFunction (δ : ℝ≥0) (x : Finset α → D → ℝ) : ℂ :=
  activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
    (booleanSiteJets sets (fun s d => x s d.val))

theorem activeAveragedSlicedIdealSiteFunction_bound (δ : ℝ≥0) (hδ : 0 < δ)
    (x : Finset α → D → ℝ) :
    ‖activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ x‖ ≤
      (δ⁻¹ ^ Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ≥0) := by
  have hx := (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ center width).1
    (booleanSiteJets sets (fun s d => x s d.val))
  simpa only [activeAveragedSlicedIdealSiteFunction, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx.1] using hx.2

theorem activeAveragedSlicedIdealSiteFunction_lipschitz (δ : ℝ≥0) (hδ : 0 < δ) :
    LipschitzWith
      (affineProductProfileLip (Σ d : {d // ¬P d}, O d.val) δ * (2 : ℝ≥0)^Fintype.card α)
      (activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ) := by
  have hrestrict : LipschitzWith 1
      (fun x : Finset α → D → ℝ => fun s (d : {d // ¬P d}) => x s d.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro s
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro d
    exact (dist_le_pi_dist (x s) (y s) d.val).trans (dist_le_pi_dist x y s)
  have hi := (activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ center width).2.1
  change LipschitzWith _ (fun x : Finset α → D → ℝ =>
    (activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
      (booleanSiteJets sets (fun s d => x s d.val)) : ℂ))
  simpa only [one_mul, mul_one, Function.comp_def] using
    Complex.isometry_ofReal.lipschitzWith.comp
      (hi.comp ((booleanSiteJets_lipschitz sets).comp hrestrict))

theorem exists_active_sliced_ideal_site_approximation (δ : ℝ≥0) (hδ : 0 < δ)
    {R ε p : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*Q+8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ)
        (f : (Finset α × D → Fin n) → Finset α → (D → ℝ) → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α)*Fintype.card D : ℕ)*(4*Q+8)+Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*Q+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Finset α → D → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖(activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets δ center width
              (booleanSiteJets sets (fun s d => x s d.val)) : ℂ) -
            ∑ k, a k*∏ s, f k s (x s)‖ ≤ ε := by
  intro Q
  have hcard : Fintype.card (Σ d : {d // ¬P d}, O d.val) ≤ Fintype.card (Σ d, O d) := by
    apply Fintype.card_le_of_injective (fun a : (Σ d : {d // ¬P d}, O d.val) =>
      (⟨a.1.val, a.2⟩ : Σ d, O d))
    rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ heq
    cases heq
    rfl
  have hcardR : (Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ) ≤
      Fintype.card (Σ d, O d) := by exact_mod_cast hcard
  have hQle : idealSiteLogBudget (Fintype.card (Σ d : {d // ¬P d}, O d.val))
      (Fintype.card α) p ≤ Q := by
    dsimp only [Q, idealSiteLogBudget, affineProfileLogBound]
    gcongr
  have hb := idealSiteLogBudget_bounds (Fintype.card (Σ d, O d)) (Fintype.card α) hp
  have hprof := idealSiteProfile_bounds (Σ d : {d // ¬P d}, O d.val)
    (Fintype.card α) δ hδ hp hδp
  exact exists_grouped_site_approximation
    (activeAveragedSlicedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets center width δ)
    (δ⁻¹ ^ Fintype.card (Σ d : {d // ¬P d}, O d.val))
    (affineProductProfileLip (Σ d : {d // ¬P d}, O d.val) δ * (2 : ℝ≥0)^Fintype.card α)
    (activeAveragedSlicedIdealSiteFunction_bound h P sets center width δ hδ)
    (activeAveragedSlicedIdealSiteFunction_lipschitz h P sets center width δ hδ)
    hR hε hb.1 (hRp.trans (Real.exp_le_exp.mpr hb.2.1))
    (hprof.1.trans (Real.exp_le_exp.mpr hQle))
    (hprof.2.trans (Real.exp_le_exp.mpr hQle))
    (hεp.trans (Real.exp_le_exp.mpr hb.2.1))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n
local notation "extra" => (fun g a => (g, a) : G → Option α → G × Option α)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B degree grid

noncomputable def allocatedProfileFrozenNoise :
    PartitionedProfileNoiseIndex G (G × Option α) α B degree grid → ℝ :=
  Sum.elim fixedReal (fun _ => 0)

theorem allocatedProfileFrozenNoise_abs_le
    (j : PartitionedProfileNoiseIndex G (G × Option α) α B degree grid) :
    |allocatedProfileFrozenNoise B U basis S x u j| ≤ 1 := by
  cases j with
  | inl j => exact allocatedPartitionedInput_frozen_bound B U basis S x u j
  | inr j => simp only [allocatedProfileFrozenNoise, Sum.elim_inr, abs_zero, zero_le_one]

omit [∀ j, Fintype (I j)] in
theorem allocatedTailRatio_abs_le {t : ℝ} (ht : 0 < t) (hσ : ∀ j, |σ j| ≤ t)
    (a : LayerSamplerAxis I n) : |σ a.1 / t| ≤ 1 := by
  rw [abs_div, abs_of_pos ht]
  exact (div_le_one ht).mpr (hσ a.1)

variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedTailProfileJet_eq {t : ℝ} (ht : t ≠ 0)
    (r : activeCoefficient → ℝ) (y : activeInput → ℝ) :
    partitionedAllocatedProfileJet degree grid extra (fun a : {a // ¬grid a} => rows a.val.1)
        (fun a => R a.1) t
        (profileNoiseWithActive degree grid (allocatedProfileFrozenNoise B U basis S x u)
          (activeTailRescale degree grid (fun a => σ a.1 / t) r)) y =
      allocatedNormalizedLongJetMap B U basis S x u rows y r := by
  let z := profileNoiseWithActive degree grid (allocatedProfileFrozenNoise B U basis S x u)
    (activeTailRescale degree grid (fun a => σ a.1 / t) r)
  have hcube (v : Finset α) :
      normalizedCubeTuple (partitionedProfileInput grid extra) z y v =
        normalizedCubeTuple (partitionedPrincipalInput grid extra) fixedReal y v := by
    funext k
    rw [partitionedProfileInput_source]
    rfl
  have htail (j : Fin m) (N : ℕ) : tailProfileSize (R j) (σ j) N =
      σ j * tailProfileSize (R j) 1 N := by
    unfold tailProfileSize
    ring
  have hpoly (a : {a // ¬grid a}) :
      monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B degree a.val =>
        coefficientProfileCenter (principalCoefficientSlots degree a.val)
            (principalProfileSize (R a.val.1) (Fintype.card (B a.val))) e +
          coefficientProfileWidth (principalCoefficientSlots degree a.val) (constantCoefficientSlot _ _)
            (R a.val.1 / 4) (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
            (t * tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val))) e *
              z (.inr ⟨a.val, e⟩)) =
        allocatedAxisProfilePolynomial B R σ a.val (fun e => r ⟨a, e⟩) := by
    rw [allocatedAxisProfilePolynomial_eq]
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [z]
    rw [profileNoiseWithActive_active, htail]
    unfold activeTailRescale
    congr 1
    exact boundedProfileWidth_noise_rescale degree a.val (R a.val.1 / 4)
      (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
      (tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val)))
      (σ a.val.1) t (r ⟨a, e⟩) ht e
  change partitionedAllocatedProfileJet degree grid extra (fun a : {a // ¬grid a} => rows a.val.1)
    (fun a => R a.1) t z y = _
  funext o
  unfold partitionedAllocatedProfileJet partitionedProfileJet
  simp_rw [hcube, hpoly]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
