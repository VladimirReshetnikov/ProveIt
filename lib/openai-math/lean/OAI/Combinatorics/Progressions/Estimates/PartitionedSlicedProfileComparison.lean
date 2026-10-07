/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_partitioned_sliced_profile_comparison_with_scales
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
    let ideal := fun a => regularizedImageDensity
      (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))
      (fun x => jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)) sets (slice a x)) ρ
    let post := fun a (y : (Σ d, O d) → ℝ) o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z a)) o + y o)
    |(∫ p, ideal p.1 p.2 * f (p.1, post p.1 p.2) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) (slice p.1 p.2))
        ∂μ.prod (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  classical
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hcomp⟩ := exists_retained_sliced_coefficient_source_with_scales
    (Ω := Ω) (Z := PartitionedProfileNoiseIndex G Z α B h P) (K₀ := SamplerTupleIndex G B h)
    (fun d : {d // ¬P d} => h d.val) (fun d => hh d.val) sets hsets hcard block hblock
    (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    (fun d => unitProfilePrincipalSize_pos (B := B) d.val)
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d.val).le)
    ψ hψ hrange hzero hone A T hLip hTransition degree (fun d => hdegree d.val)
    1 1 zero_le_one zero_le_one δ hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro z hz center width hcenter hwidth μ hμ hgood R f hf hfb slice ideal post
  let c := fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a => c a d b) := by
    dsimp [c, partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  let F : Ω × ((Σ d, O d) → ℝ) → Ω × ((Σ d, O d) → ℝ) := fun p =>
    (p.1, fun o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z p.1)) o + p.2 o))
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    have hzj := (hz (.inr ⟨o.1.val, constantCoefficientSlot _ _⟩)).comp
      (measurable_fst : Measurable (Prod.fst : Ω × ((Σ d, O d) → ℝ) → Ω))
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
  have hcoeff : ∀ᵐ a ∂μ,
      (∀ d o, unitProfilePrincipalSize (B := B) d.val ≤ |c a d (block d o)|) ∧
      (∀ d o, |c a d (block d o)| ≤ 2 * unitProfilePrincipalSize (B := B) d.val) ∧
      (∀ d, (∑ b, |c a d b|) ≤ 1) ∧ (∀ i, δ ≤ |width a i|) ∧
      (∀ i, |center a i| + |width a i| ≤ 1) ∧ (∀ j, |z a j| ≤ 1) := by
    filter_upwards [hgood] with a ha
    exact ⟨fun d o => (partitionedProfilePrincipal_unit_bounds h P (z a) ha.1 d (block d o)).1,
      fun d o => (partitionedProfilePrincipal_unit_bounds h P (z a) ha.1 d (block d o)).2,
      partitionedProfilePrincipal_unit_sum h P (z a) ha.1, ha.2.1, ha.2.2, ha.1⟩
  have he := hcomp (fun d : {d // ¬P d} => SamplerCoefficientSlot G B h d.val)
    (partitionedProfileTerms (G := G) (B := B) h P)
    (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
    (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra)
    (fun d e _ => e.property.trans (hdegree d.val)) (partitionedProfileTail_unit_sum h P)
    c center width z hc hcenter hwidth hz μ hμ hcoeff (f ∘ F) (hf.comp hF) (fun p => hfb (F p))
  dsimp only [Function.comp_apply] at he
  simp_rw [hFactual] at he
  exact he

theorem exists_partitioned_sliced_profile_comparison
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
    let ideal := fun a => regularizedImageDensity
      (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))
      (fun x => jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)) sets (slice a x)) ρ
    let post := fun a (y : (Σ d, O d) → ℝ) o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z a)) o + y o)
    |(∫ p, ideal p.1 p.2 * f (p.1, post p.1 p.2) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) (slice p.1 p.2))
        ∂μ.prod (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  obtain ⟨ρ, hρ, hρone, _, t, ht, htone, _, hs⟩ :=
    exists_partitioned_sliced_profile_comparison_with_scales (Ω := Ω)
      h hh P extra sets hsets hcard block hblock ψ hψ hrange hzero hone A T hLip hTransition
      hdegree hδ hδone hE
  exact ⟨ρ, hρ, hρone, t, ht, htone, hs⟩

end Erdos3

end

end OAI
