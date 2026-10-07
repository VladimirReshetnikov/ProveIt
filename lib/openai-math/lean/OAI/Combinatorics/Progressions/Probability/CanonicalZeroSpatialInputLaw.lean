/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastMeanRiemann

namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

theorem canonicalZeroSpatialInputSource_sigma {X : Type*} [Fintype X]
    (I : X → Type*) [∀ x, Fintype (I x)] :
    unitCoefficientSource (Σ x, I x) =
      sigmaAxisMeasure (fun x => unitCoefficientSource (I x)) := by
  symm
  simp only [unitCoefficientSource]
  rw [sigmaAxisMeasure_density]
  · congr 1
    funext u
    exact (Fintype.prod_sigma (fun a : Σ x, I x => smoothProbabilityProfile (u a))).symm
  · intro x
    exact (smoothProductProfile_contDiff _).continuous.integrable_of_hasCompactSupport
      (smoothProductProfile_compact _)
  · intro x u
    exact (smoothProductProfile_range _ _).1

theorem unitCoefficientSource_split (J I : Type*) [Fintype J] [Fintype I] :
    (unitCoefficientSource (J ⊕ I)).map
        (fun u => ((fun j => u (.inl j)), (fun i => u (.inr i)))) =
      realDensityMeasure volume (smoothSplitProfile J I) := by
  have h := realDensityMeasure_map_equiv
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)) volume
    (smoothProductProfile (J ⊕ I))
  rw [(volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).map_eq] at h
  exact h.trans (by congr 1; funext p; exact (smoothSplitProfile_join J I p).symm)

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ)

noncomputable def canonicalZeroSpatialInputIndex :
    (UnselectedColumn s ⊕ (Unit ⊕ Empty)) ≃ Option Zsp where
  toFun := Sum.elim (fun j => some j.val) (Sum.elim (fun _ => none) Empty.elim)
  invFun := fun j => match j with
    | none => .inr (.inl ())
    | some j => .inl ⟨j, by rintro ⟨i, hi⟩; exact Empty.elim i⟩
  left_inv := by
    intro i
    rcases i with j | (u | e)
    · rfl
    · cases u; rfl
    · exact Empty.elim e
  right_inv := by intro j; cases j <;> rfl

noncomputable def canonicalZeroSpatialInputMap
    (u : Option Zsp × X → ℝ) (a : Σ _ : X, Unit ⊕ Empty) : ℝ :=
  canonicalSpatialKernelMap s root D (W := W) (L := L)
    ((fun j => u (some j.val, a.1)),
      (fun i => match i with | .inl _ => u (none, a.1) | .inr e => Empty.elim e)) a.2

theorem canonicalZeroSpatialKernelMap_measurable :
    Measurable (canonicalSpatialKernelMap s root D (W := W) (L := L)) := by
  unfold canonicalSpatialKernelMap
  exact ((matrixSupCLM _).continuous.measurable.comp measurable_snd).add
    ((matrixSupCLM _).continuous.measurable.comp measurable_fst)

omit [Fintype X] in
theorem canonicalZeroSpatialInputMap_measurable :
    Measurable (canonicalZeroSpatialInputMap (X := X) s root D W L) := by
  apply Measurable.of_eval
  intro a
  apply (measurable_pi_apply a.2).comp
  apply (canonicalZeroSpatialKernelMap_measurable s root D W L).comp
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun j => measurable_pi_apply (some j.val, a.1))
  · apply Measurable.of_eval
    intro i
    cases i with
    | inl u => exact measurable_pi_apply (none, a.1)
    | inr e => exact Empty.elim e

noncomputable def canonicalZeroSpatialFlatIndex :
    (Option Zsp × X) ≃ (Σ _ : X, UnselectedColumn s ⊕ (Unit ⊕ Empty)) where
  toFun := fun p => ⟨p.2, (canonicalZeroSpatialInputIndex s).symm p.1⟩
  invFun := fun a => (canonicalZeroSpatialInputIndex s a.2, a.1)
  left_inv := by intro p; simp
  right_inv := by intro a; simp

theorem canonicalZeroSpatialInputMap_law :
    (realDensityMeasure volume (smoothProductProfile (Option Zsp × X))).map
        (canonicalZeroSpatialInputMap (X := X) s root D W L) =
      canonicalZeroSpatialLaw (X := X) s root D W L := by
  let split := fun u : UnselectedColumn s ⊕ (Unit ⊕ Empty) → ℝ =>
    ((fun j => u (.inl j)), (fun i => u (.inr i)))
  let site := canonicalSpatialKernelMap s root D (W := W) (L := L) ∘ split
  have hsplit : Measurable split := by fun_prop
  have hsite : Measurable site :=
    (canonicalZeroSpatialKernelMap_measurable s root D W L).comp hsplit
  have hlaw : (unitCoefficientSource (UnselectedColumn s ⊕ (Unit ⊕ Empty))).map site =
      (realDensityMeasure volume (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ Empty))).map
        (canonicalSpatialKernelMap s root D (W := W) (L := L)) := by
    rw [show site = canonicalSpatialKernelMap s root D (W := W) (L := L) ∘ split from rfl,
      ← Measure.map_map (canonicalZeroSpatialKernelMap_measurable s root D W L) hsplit,
      unitCoefficientSource_split]
  let e := canonicalZeroSpatialFlatIndex (X := X) s
  let reindex := fun u : Option Zsp × X → ℝ => u ∘ e.symm
  have hr : Measurable reindex := by fun_prop
  have hs : Measurable (sigmaAxisSampler (fun _ : X => site)) :=
    sigmaAxisSampler_measurable _ (fun _ => hsite)
  have he : canonicalZeroSpatialInputMap (X := X) s root D W L =
      sigmaAxisSampler (fun _ : X => site) ∘ reindex := by
    funext u a
    rfl
  rw [he, ← Measure.map_map hs hr]
  change ((unitCoefficientSource (Option Zsp × X)).map (fun u => u ∘ e.symm)).map _ = _
  rw [unitCoefficientSource_reindex e, canonicalZeroSpatialInputSource_sigma,
    sigmaAxisSampler_image_law _ _ (fun _ => hsite)]
  simp_rw [hlaw]
  rfl

theorem canonicalZeroSpatialInputMap_integral_complex
    (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ) (hφ : Measurable φ) :
    (∫ y, φ y ∂canonicalZeroSpatialLaw (X := X) s root D W L) =
      ∫ u, (smoothProductProfile (Option Zsp × X) u : ℂ) *
        φ (canonicalZeroSpatialInputMap (X := X) s root D W L u) := by
  rw [← canonicalZeroSpatialInputMap_law s root D W L,
    integral_map (canonicalZeroSpatialInputMap_measurable s root D W L).aemeasurable
      hφ.aestronglyMeasurable,
    realDensityMeasure_integral_complex volume _
      (smoothProductProfile_contDiff _).continuous.measurable
      (fun u => (smoothProductProfile_range _ u).1)]

end Erdos3

end

end OAI
