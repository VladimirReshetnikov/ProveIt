/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Probability.PartitionedSlicedDensityComparison

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_active_tail_sliced_profile_comparison_with_scales
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    {δ E : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ E ∧
    ∀ τ : D → ℝ, (∀ d, |τ d| ≤ 1) →
    ∀ z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
    ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
    ∀ (R : D → ℝ) (f : W × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    |(∫ p, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width p.2 *
        f (p.1, fun o => R o.1.val * p.2 o) ∂μ.prod volume) -
      ∫ p, f (p.1.1, partitionedAllocatedProfileJet h P extra sets R t
          (profileNoiseWithActive h P (z p.1.1) (activeTailRescale h P τ p.1.2))
          (fun i => center i + width i * p.2 i))
        ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
          (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  classical
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_partitioned_sliced_density_comparison_with_scales
    (Ω := W × (ActiveProfileCoefficientIndex G B h P → ℝ))
    h hh P extra sets hsets hcard block hblock ψ hψ hrange hzero hone A T hLip hTransition
    hdegree hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro τ hτ z hz center width hwidth hcenter μ hμ hbox R f hf hbound
  let : IsProbabilityMeasure μ := hμ
  let ζ := fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) =>
    profileNoiseWithActive h P (z p.1) (activeTailRescale h P τ p.2)
  have hζ (j : PartitionedProfileNoiseIndex G Z α B h P) : Measurable (fun p => ζ p j) :=
    profileNoiseWithActive_measurable h P
      (fun p : W × (ActiveProfileCoefficientIndex G B h P → ℝ) => z p.1)
      (fun p => activeTailRescale h P τ p.2)
      (fun i => (hz i).comp measurable_fst)
      (activeTailRescale_measurable_comp h P τ Prod.snd
        (fun i => (measurable_pi_apply i).comp measurable_snd)) j
  have hgood : ∀ᵐ p ∂μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)),
      (∀ j, |ζ p j| ≤ 1) ∧ (∀ i, δ ≤ |width i|) ∧ (∀ i, |center i| + |width i| ≤ 1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbox,
      Measure.quasiMeasurePreserving_snd.ae
        (unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P))] with p hp hr
    exact ⟨profileNoiseWithActive_abs_le h P (z p.1) (activeTailRescale h P τ p.2) hp
      (activeTailRescale_abs_le h P τ hτ p.2 hr), hwidth, hcenter⟩
  let f' := fun p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) ×
      ((Σ d, O d) → ℝ) => f (p.1.1, p.2)
  have hf' : Measurable f' := hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have he := hs ζ hζ (fun _ => center) (fun _ => width)
    (fun _ => measurable_const) (fun _ => measurable_const)
    (μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))) inferInstance hgood
    R f' hf' (fun p => hbound (p.1.1, p.2))
  dsimp only at he
  simp only [ζ, partitionedSlicedRegularizedIdeal_activeTailRescale] at he
  let Φ := fun p : W × ((Σ d, O d) → ℝ) => f (p.1, fun o => R o.1.val * p.2 o)
  have hΦ : Measurable Φ := hf.comp (measurable_fst.prodMk (Measurable.of_eval
    (fun o => measurable_const.mul ((measurable_pi_apply o).comp measurable_snd))))
  have havg := retained_coefficient_density_average μ
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeSlicedProfileIdeal Z h P sets ρ center width)
    (activeSlicedProfileIdeal_measurable Z h P sets ρ center width)
    (fun r => partitionedSlicedRegularizedIdeal_probability h P sets ρ hρ center width
      (profileNoiseWithActive (Z := Z) h P (fun _ => 0) r)) Φ hΦ
    (fun p => hbound (p.1, fun o => R o.1.val * p.2 o))
  change |(∫ p : (W × (ActiveProfileCoefficientIndex G B h P → ℝ)) × ((Σ d, O d) → ℝ),
      activeSlicedProfileIdeal Z h P sets ρ center width p.1.2 p.2 * Φ (p.1.1, p.2)
      ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod volume) - _| ≤ E at he
  rw [havg] at he
  exact he

theorem exists_active_tail_sliced_profile_comparison
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    {δ E : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    ∀ τ : D → ℝ, (∀ d, |τ d| ≤ 1) →
    ∀ z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
    ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
    ∀ (R : D → ℝ) (f : W × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    |(∫ p, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width p.2 *
        f (p.1, fun o => R o.1.val * p.2 o) ∂μ.prod volume) -
      ∫ p, f (p.1.1, partitionedAllocatedProfileJet h P extra sets R t
          (profileNoiseWithActive h P (z p.1.1) (activeTailRescale h P τ p.1.2))
          (fun i => center i + width i * p.2 i))
        ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
          (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  obtain ⟨ρ, hρ, hρone, _, t, ht, htone, _, hs⟩ :=
    exists_active_tail_sliced_profile_comparison_with_scales (W := W)
      h hh P extra sets hsets hcard block hblock ψ hψ hrange hzero hone A T hLip hTransition
      hdegree hδ hδone hE
  exact ⟨ρ, hρ, hρone, t, ht, htone, hs⟩

end Erdos3

end

end OAI
