/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
import OAI.Combinatorics.Progressions.Estimates.PartitionedSlicedProfileComparison

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_translate_test {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (μ : Measure W) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U : W × X → I → ℝ) (hU : Measurable U) (b : W → I → ℝ) (hb : Measurable b)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (φ : W × (I → ℝ) → ℝ) (hφ : Measurable φ)
    (hbound : ∀ p, ‖φ p‖ ≤ 1) :
    (∫ p, regularizedImageDensity ν (fun x => b p.1 + U (p.1, x)) ρ p.2 * φ p ∂μ.prod volume) =
      ∫ p, regularizedImageDensity ν (fun x => U (p.1, x)) ρ p.2 * φ (p.1, b p.1 + p.2)
        ∂μ.prod volume := by
  have hshift : Measurable (fun p : W × X => b p.1 + U p) := (hb.comp measurable_fst).add hU
  have hD := conditionalRegularizedDensity_measurable ν U hU ρ
  have hDshift := conditionalRegularizedDensity_measurable ν _ hshift ρ
  have hprob (w) := regularizedImageDensity_probability ν (fun x => U (w, x))
    (hU.comp (measurable_const.prodMk measurable_id)) ρ hρ
  have hprobshift (w) := regularizedImageDensity_probability ν (fun x => b w + U (w, x))
    (hshift.comp (measurable_const.prodMk measurable_id)) ρ hρ
  have hi := (densityMixture_joint_integrable μ volume _ hDshift
    (Filter.Eventually.of_forall hprobshift)).mul_bdd hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have htest : Measurable (fun p : W × (I → ℝ) => φ (p.1, b p.1 + p.2)) :=
    hφ.comp (measurable_fst.prodMk ((hb.comp measurable_fst).add measurable_snd))
  have hj := (densityMixture_joint_integrable μ volume _ hD
    (Filter.Eventually.of_forall hprob)).mul_bdd htest.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hbound (p.1, b p.1 + p.2)))
  dsimp only [Function.uncurry] at hi hj
  rw [integral_prod _ hi, integral_prod _ hj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => regularizedImageDensity_translate_test ν _
    (hU.comp (measurable_const.prodMk measurable_id)) ρ hρ (b w) (fun y => φ (w, y))
    (hφ.comp (measurable_const.prodMk measurable_id)))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_partitioned_sliced_density_comparison_with_scales
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
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
    ∀ (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ),
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ j, |z a j| ≤ 1) ∧ (∀ i, δ ≤ |width a i|) ∧
      (∀ i, |center a i| + |width a i| ≤ 1)) →
    ∀ (R : D → ℝ) (f : Ω × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    let slice := fun a x i => center a i + width a i * x i
    let ideal := fun a => partitionedSlicedRegularizedIdeal h P sets ρ (center a) (width a) (z a)
    let post := fun (y : (Σ d, O d) → ℝ) o => R o.1.val * y o
    |(∫ p, ideal p.1 p.2 * f (p.1, post p.2) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) (slice p.1 p.2))
        ∂μ.prod (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  classical
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_partitioned_sliced_profile_comparison_with_scales
    (Ω := Ω) h hh P extra sets hsets hcard block hblock ψ hψ hrange hzero hone A T hLip hTransition
    hdegree hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro z hz center width hb hw μ hμ hgood R f hf hbound slice ideal post
  let : IsProbabilityMeasure μ := hμ
  let source := jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val)
  let U := fun p : Ω ×
    (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z p.1)) sets (slice p.1 p.2)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a =>
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a) d b) := by
    dsimp [partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  have hU : Measurable U := jointBooleanSampler_measurable_comp
    (Ω := Ω × (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ))
    (fun d : {d // ¬P d} => h d.val) sets _ (fun d b => (hc d b).comp measurable_fst)
    (fun p => slice p.1 p.2) (fun i => ((hb i).comp measurable_fst).add
      (((hw i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)))
  let b := fun a => booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z a))
  have hbm : Measurable b := by
    apply booleanConstantJet_measurable_comp
    intro d
    exact measurable_const.mul (hz _)
  let φ := fun p : Ω × ((Σ d, O d) → ℝ) => f (p.1, post p.2)
  have hφ : Measurable φ := hf.comp (measurable_fst.prodMk (Measurable.of_eval
    (fun o => measurable_const.mul ((measurable_pi_apply o).comp measurable_snd))))
  have heq := conditionalRegularizedDensity_translate_test μ source U hU b hbm ρ hρ φ hφ
    (fun p => hbound (p.1, post p.2))
  have he := hs z hz center width hb hw μ hμ hgood R f hf hbound
  dsimp only at he
  change (∫ p, ideal p.1 p.2 * f (p.1, post p.2) ∂μ.prod volume) =
    (∫ p, regularizedImageDensity source (fun x => U (p.1, x)) ρ p.2 *
      f (p.1, fun o => R o.1.val * (b p.1 o + p.2 o)) ∂μ.prod volume) at heq
  rw [heq]
  exact he

theorem exists_partitioned_sliced_density_comparison
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
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
    ∀ (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ),
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ j, |z a j| ≤ 1) ∧ (∀ i, δ ≤ |width a i|) ∧
      (∀ i, |center a i| + |width a i| ≤ 1)) →
    ∀ (R : D → ℝ) (f : Ω × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    let slice := fun a x i => center a i + width a i * x i
    let ideal := fun a => partitionedSlicedRegularizedIdeal h P sets ρ (center a) (width a) (z a)
    let post := fun (y : (Σ d, O d) → ℝ) o => R o.1.val * y o
    |(∫ p, ideal p.1 p.2 * f (p.1, post p.2) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) (slice p.1 p.2))
        ∂μ.prod (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  obtain ⟨ρ, hρ, hρone, _, t, ht, htone, _, hs⟩ :=
    exists_partitioned_sliced_density_comparison_with_scales (Ω := Ω)
      h hh P extra sets hsets hcard block hblock ψ hψ hrange hzero hone A T hLip hTransition
      hdegree hδ hδone hE
  exact ⟨ρ, hρ, hρone, t, ht, htone, hs⟩

end Erdos3

end

end OAI
