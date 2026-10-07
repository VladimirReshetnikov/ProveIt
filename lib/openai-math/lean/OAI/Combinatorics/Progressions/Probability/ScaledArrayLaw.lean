/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Construct mapped probability instances from the existing measurable chart maps.
Mathematical statements are unchanged. -/
import OAI.Compat.BigOperators
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.MixedArrayReference
import OAI.Combinatorics.Progressions.Geometry.QuantitativeProjectedChart
import OAI.Combinatorics.Progressions.Polynomial.MixedPolynomialChart
import OAI.Combinatorics.Progressions.Probability.ScaledCoefficientLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule Set

variable {D : Type*} [Fintype D] {n : ℕ}

noncomputable def normalizedQuotientDensity (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (Ω : Set (EuclideanSpace ℝ D)) (f : W × (Fin n → ℤ) → ℝ) :
    (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ :=
  restrictedChartDensity (normalizedLatticeQuotient W b hb) (normalizedLatticePoint W b ⁻¹' Ω)
    (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)) f

theorem normalizedQuotientDensity_apply (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) {x : W × (Fin n → ℤ)} (hx : normalizedLatticePoint W b x ∈ Ω) :
    normalizedQuotientDensity W b hb Ω f (normalizedLatticeQuotient W b hb x) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * f x :=
  restrictedChartDensity_apply _ _ _ _ (normalizedLatticeQuotient_injOn W b hb hΩ) hx

theorem normalizedQuotientDensity_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : Measurable f) :
    Measurable (normalizedQuotientDensity W b hb Ω f) :=
  embeddingDensity_measurable _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ) _ _
    (hf.comp measurable_subtype_coe)

theorem normalizedQuotientDensity_nonneg (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : ∀ x, 0 ≤ f x) (y) :
    0 ≤ normalizedQuotientDensity W b hb Ω f y :=
  embeddingDensity_nonneg _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ).injective
    (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le _
    (fun x => hf x.val) y

theorem normalizedQuotientDensity_bound (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x, ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * f x ≤ B) (y) :
    normalizedQuotientDensity W b hb Ω f y ≤ B :=
  embeddingDensity_bound _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ).injective hB _
    (fun x => hf x.val) y

theorem normalizedQuotientDensity_law (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : ∀ x, normalizedLatticePoint W b x ∉ Ω → f x = 0) :
    Measure.map (normalizedLatticeQuotient W b hb)
      (realDensityMeasure (volume.prod (Measure.count : Measure (Fin n → ℤ))) f) =
      realDensityMeasure μ (normalizedQuotientDensity W b hb Ω f) :=
  restrictedChartDensity_law _ (normalizedLatticeQuotient_measurable W b hb)
    (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_embedding W b hb hΩm hΩ) _ μ
    (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le
    (normalizedLatticeQuotient_map_restrict W b hb μ hΩm hΩ) f hf

end Erdos3

end

section

namespace Erdos3

open Module Submodule Set

theorem restrictedChartDensity_recover {X Y : Type*} (q : X → Y) (S : Set X)
    (c : ℝ) (f : X → ℝ) (hinj : Set.InjOn q S) {y : Y}
    (hy : restrictedChartDensity q S c f y ≠ 0) :
    ∃ x, x ∈ S ∧ q x = y ∧ f x ≠ 0 := by
  have hm : y ∈ q '' S := by
    by_contra hn
    exact hy (restrictedChartDensity_zero q S c f hn)
  obtain ⟨x, hx, rfl⟩ := hm
  refine ⟨x, hx, rfl, ?_⟩
  rw [restrictedChartDensity_apply q S c f hinj hx] at hy
  exact (mul_ne_zero_iff.mp hy).2

theorem restrictedChartDensity_nonzero_iff {X Y : Type*} (q : X → Y) (S : Set X)
    (c : ℝ) (hc : c ≠ 0) (f : X → ℝ) (hinj : Set.InjOn q S) (y : Y) :
    restrictedChartDensity q S c f y ≠ 0 ↔ ∃ x, x ∈ S ∧ q x = y ∧ f x ≠ 0 := by
  constructor
  · exact restrictedChartDensity_recover q S c f hinj
  · rintro ⟨x, hx, rfl, hf⟩
    rw [restrictedChartDensity_apply q S c f hinj hx]
    exact mul_ne_zero hc hf

theorem normalizedQuotientDensity_recover {D : Type*} [Fintype D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ)
    {y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : normalizedQuotientDensity W b hb Ω f y ≠ 0) :
    ∃ x, normalizedLatticePoint W b x ∈ Ω ∧ normalizedLatticeQuotient W b hb x = y ∧ f x ≠ 0 :=
  restrictedChartDensity_recover _ _ _ _ (normalizedLatticeQuotient_injOn W b hb hΩ) hy

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem mixedCoefficient_quotient_law (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (e : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : (Fin n) → PMF ℤ)
    (hsupport : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart e x) ∈ Ω) :
    Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart e x))
      (mixedCoefficientLaw c w p) =
      realDensityMeasure μ (normalizedQuotientDensity W b hb Ω (orthonormalMixedDensity e c w p)) := by
  change Measure.map (normalizedLatticeQuotient W b hb ∘ orthonormalMixedChart e)
    (mixedCoefficientLaw c w p) = _
  rw [← Measure.map_map (normalizedLatticeQuotient_measurable W b hb) (orthonormalMixedChart e).measurable,
    orthonormalMixedDensity_law e c w hw p]
  apply normalizedQuotientDensity_law W b hb μ hΩm hΩ
  intro x hx
  by_contra hf
  have h := hsupport ((orthonormalMixedChart e).symm x) hf
  rw [(orthonormalMixedChart e).apply_symm_apply] at h
  exact hx h

theorem mixedCoefficient_quotient_density (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (e : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : (Fin n) → PMF ℤ)
    (hsupport : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart e x) ∈ Ω)
    {B : ℝ} (hB : 0 ≤ B)
    (hcap : ∀ x, ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
      mixedCoefficientDensity c w p x ≤ B) :
    ∃ F : (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ,
      Measurable F ∧ (∀ y, 0 ≤ F y ∧ F y ≤ B) ∧ Integrable F μ ∧ (∫ y, F y ∂μ) = 1 ∧
      Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart e x))
        (mixedCoefficientLaw c w p) = realDensityMeasure μ F ∧
      ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
        F (normalizedLatticeQuotient W b hb (orthonormalMixedChart e x)) =
          ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
            mixedCoefficientDensity c w p x := by
  let F := normalizedQuotientDensity W b hb Ω (orthonormalMixedDensity e c w p)
  have hFm : Measurable F := normalizedQuotientDensity_measurable W b hb hΩm hΩ _
    (orthonormalMixedDensity_measurable e c w p)
  have hF0 : ∀ y, 0 ≤ F y := normalizedQuotientDensity_nonneg W b hb hΩm hΩ _
    (orthonormalMixedDensity_nonneg e c w hw p)
  have hFB : ∀ y, F y ≤ B := normalizedQuotientDensity_bound W b hb hΩm hΩ _ hB
    (fun x => hcap ((orthonormalMixedChart e).symm x))
  have hlaw := mixedCoefficient_quotient_law W b hb e μ hΩm hΩ c w hw p hsupport
  let : IsProbabilityMeasure (mixedCoefficientLaw c w p) := mixedCoefficientLaw_probability c w hw p
  have hprob : IsProbabilityMeasure (realDensityMeasure μ F) := by
    rw [← hlaw]
    exact Measure.isProbabilityMeasure_map
      ((normalizedLatticeQuotient_measurable W b hb).comp
        (orthonormalMixedChart e).measurable).aemeasurable
  let : IsProbabilityMeasure (realDensityMeasure μ F) := hprob
  obtain ⟨hFi, hFmass⟩ := boundedDensity_mass μ F hFm hF0 hFB
  refine ⟨F, hFm, fun y => ⟨hF0 y, hFB y⟩, hFi, hFmass, hlaw, ?_⟩
  intro x hx
  have h := normalizedQuotientDensity_apply W b hb hΩ (orthonormalMixedDensity e c w p) (hsupport x hx)
  simpa only [orthonormalMixedDensity, MeasurableEquiv.symm_apply_apply] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalMixedDensity (c w : I → ℝ) (p : Fin n → PMF ℤ) :
    (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ :=
  normalizedQuotientDensity W b hb (standardLatticeSmallBox D) (orthonormalMixedDensity o c w p)

theorem canonicalMixedDensity_measurable (c w : I → ℝ) (p : Fin n → PMF ℤ) :
    Measurable (canonicalMixedDensity W b hb o c w p) :=
  normalizedQuotientDensity_measurable W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (orthonormalMixedDensity_measurable o c w p)

theorem canonicalMixedDensity_apply (c w : I → ℝ) (p : Fin n → PMF ℤ)
    {x : (I → ℝ) × (Fin n → ℤ)}
    (hx : normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    canonicalMixedDensity W b hb o c w p (normalizedLatticeQuotient W b hb (orthonormalMixedChart o x)) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * mixedCoefficientDensity c w p x := by
  exact (normalizedQuotientDensity_apply W b hb (Subset.rfl) (orthonormalMixedDensity o c w p) hx).trans
    (by simp only [orthonormalMixedDensity, MeasurableEquiv.symm_apply_apply])

theorem canonicalMixedDensity_recover (c w : I → ℝ) (p : Fin n → PMF ℤ)
    {y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalMixedDensity W b hb o c w p y ≠ 0) :
    ∃ x : (I → ℝ) × (Fin n → ℤ),
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D ∧
      normalizedLatticeQuotient W b hb (orthonormalMixedChart o x) = y ∧
      mixedCoefficientDensity c w p x ≠ 0 := by
  obtain ⟨x, hx, hq, hf⟩ := normalizedQuotientDensity_recover W b hb (Subset.rfl)
    (orthonormalMixedDensity o c w p) hy
  refine ⟨(orthonormalMixedChart o).symm x, ?_, ?_, hf⟩
  · simpa only [MeasurableEquiv.apply_symm_apply] using hx
  · simpa only [MeasurableEquiv.apply_symm_apply] using hq

theorem canonicalMixedDensity_nonneg
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ) (y) :
    0 ≤ canonicalMixedDensity W b hb o c w p y :=
  normalizedQuotientDensity_nonneg W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (orthonormalMixedDensity_nonneg o c w hw p) y

theorem canonicalMixedDensity_bound
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ) (y) :
    canonicalMixedDensity W b hb o c w p y ≤
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * profileWidthFactor w := by
  have hv := (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le
  exact normalizedQuotientDensity_bound W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (mul_nonneg hv (profileWidthFactor_pos w hw).le)
    (fun x => mul_le_mul_of_nonneg_left (mixedCoefficientDensity_width_cap c w hw p ((orthonormalMixedChart o).symm x)) hv) y

theorem canonicalMixedDensity_law
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart o x))
      (mixedCoefficientLaw c w p) = realDensityMeasure μ (canonicalMixedDensity W b hb o c w p) :=
  mixedCoefficient_quotient_law W b hb o μ (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) c w hw p hs

theorem canonicalMixedDensity_mass
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Integrable (canonicalMixedDensity W b hb o c w p) μ ∧
      (∫ y, canonicalMixedDensity W b hb o c w p y ∂μ) = 1 := by
  have hlaw := canonicalMixedDensity_law W b hb o μ c w hw p hs
  let : IsProbabilityMeasure (mixedCoefficientLaw c w p) := mixedCoefficientLaw_probability c w hw p
  let : IsProbabilityMeasure (realDensityMeasure μ (canonicalMixedDensity W b hb o c w p)) := by
    rw [← hlaw]
    exact Measure.isProbabilityMeasure_map
      ((normalizedLatticeQuotient_measurable W b hb).comp
        (orthonormalMixedChart o).measurable).aemeasurable
  exact boundedDensity_mass μ _ (canonicalMixedDensity_measurable W b hb o c w p)
    (canonicalMixedDensity_nonneg W b hb o c w hw p) (canonicalMixedDensity_bound W b hb o c w hw p)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule Set
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem constantCoefficient_quotient_density (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (e : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j)
    {C R B : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hchart : ∀ p, ‖(normalizedOrthogonalChart W b).symm p‖ ≤ C * ‖p‖)
    (hwR : ∀ i, w i ≤ R) (hδR : ∀ j, δ j ≤ R)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (hvolume : ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) ≤
      B * ∏ j, (basisAxisScale b j : ℝ)) :
    ∃ F : (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ,
      Measurable F ∧
      (∀ y, 0 ≤ F y ∧ F y ≤ B * profileWidthFactor w *
        ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j)) ∧
      Integrable F μ ∧ (∫ y, F y ∂μ) = 1 ∧
      Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart e x))
        (mixedCoefficientLaw (fun _ => 0) w (latticeConstantMass W b δ hδ)) = realDensityMeasure μ F ∧
      ∀ x, mixedCoefficientDensity (fun _ => 0) w (latticeConstantMass W b δ hδ) x ≠ 0 →
        F (normalizedLatticeQuotient W b hb (orthonormalMixedChart e x)) =
          ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
            mixedCoefficientDensity (fun _ => 0) w (latticeConstantMass W b δ hδ) x := by
  apply mixedCoefficient_quotient_density W b hb e μ
    (standardLatticeSmallBox_isOpen D).measurableSet (Subset.rfl) (fun _ => 0) w hw
    (latticeConstantMass W b δ hδ)
  · intro x hx
    exact constantCoefficient_chart_support W b e w hw δ hδ hC hR hchart hwR hδR hsmall hx
  · exact mul_nonneg (mul_nonneg hB (profileWidthFactor_pos w hw).le)
      (Finset.prod_nonneg (fun j _ => div_nonneg (by positivity) (hδ j).le))
  · intro x
    exact constantCoefficientDensity_cap w hw (fun j => (basisAxisScale b j : ℝ)) δ
      (basisAxisScale_cast_pos b) hδ hB hvolume x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedArrayQuotient (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W) (x : (I → J → ℝ) × (Fin n → J → ℤ)) :
    J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  fun j => normalizedLatticeQuotient W b hb (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j))

omit [Fintype J] in
theorem mixedArrayQuotient_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W) : Measurable (mixedArrayQuotient (J := J) W b hb o) := by
  apply Measurable.of_eval
  intro j
  exact (normalizedLatticeQuotient_measurable W b hb).comp
    ((orthonormalMixedChart o).measurable.comp
      ((measurable_pi_apply j).comp (mixedArrayRegroup I (Fin n) J).measurable))

theorem mixedArray_quotient_density (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (hcw : ∀ i j, |c i j| + w i j ≤ R)
    (hp : ∀ i j k, k ∈ (p i j).support → |(k : ℝ) / basisAxisScale b i| ≤ R) :
    ∃ F : (J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ,
      Measurable F ∧
      (∀ y, 0 ≤ F y ∧ F y ≤ ∏ j, ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        profileWidthFactor (fun i => w i j)) ∧
      Integrable F (Measure.pi (fun _ : J => μ)) ∧
      (∫ y, F y ∂Measure.pi (fun _ : J => μ)) = 1 ∧
      Measure.map (mixedArrayQuotient W b hb o) (mixedScalarArrayLaw c w p) =
        realDensityMeasure (Measure.pi (fun _ : J => μ)) F ∧
      ∀ x, (∀ j, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j)
          (mixedArrayRegroup I (Fin n) J x j) ≠ 0) →
        F (mixedArrayQuotient W b hb o x) =
          ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) ^ Fintype.card J *
            ∏ j, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j)
              (mixedArrayRegroup I (Fin n) J x j) := by
  classical
  have hv := (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le
  have hs (j : J) := mixedCoefficient_quotient_density W b hb o μ
    (standardLatticeSmallBox_isOpen D).measurableSet (Subset.rfl)
    (fun i => c i j) (fun i => w i j) (fun i => hw i j) (fun i => p i j)
    (mixedCoefficient_small_support W b o hC hR hchart hsmall _ _ (fun i => hw i j)
      (fun i => hcw i j) _ (fun i k hk => hp i j k hk))
    (mul_nonneg hv (profileWidthFactor_pos _ (fun i => hw i j)).le)
    (fun x => mul_le_mul_of_nonneg_left
      (mixedCoefficientDensity_width_cap _ _ (fun i => hw i j) _ x) hv)
  choose f hfm hfB hfi hf1 hflaw hfval using hs
  let F := fun y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup =>
    ∏ j, f j (y j)
  have hFm : Measurable F := Finset.measurable_prod _ (fun j _ => (hfm j).comp (measurable_pi_apply j))
  have hFi : Integrable F (Measure.pi (fun _ : J => μ)) := Integrable.fintype_prod_dep hfi
  refine ⟨F, hFm, ?_, hFi, ?_, ?_, ?_⟩
  · intro y
    exact ⟨Finset.prod_nonneg (fun j _ => (hfB j (y j)).1),
      Finset.prod_le_prod₀ (fun j _ => (hfB j (y j)).1) (fun j _ => (hfB j (y j)).2)⟩
  · change (∫ y, (∏ j, f j (y j)) ∂Measure.pi (fun _ : J => μ)) = 1
    rw [integral_fintype_prod_eq_prod]
    simp only [hf1, Finset.prod_const_one]
  · let q := fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart o x)
    have hq : Measurable q := (normalizedLatticeQuotient_measurable W b hb).comp (orthonormalMixedChart o).measurable
    have hqa : Measurable (fun x : J → (I → ℝ) × (Fin n → ℤ) => fun j => q (x j)) :=
      Measurable.of_eval (fun coordinate => hq.comp (measurable_pi_apply coordinate))
    have houtput : ∀ j, SigmaFinite
        (Measure.map q (mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun i => p i j))) := by
      intro j
      rw [show Measure.map q (mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun i => p i j)) =
        realDensityMeasure μ (f j) from hflaw j]
      let : IsFiniteMeasure (realDensityMeasure μ (f j)) :=
        realDensityMeasure_finite μ (f j) (hfi j) (fun y => (hfB j y).1)
      exact IsFiniteMeasure.toSigmaFinite _
    change Measure.map ((fun x j => q (x j)) ∘ mixedArrayRegroup I (Fin n) J) (mixedScalarArrayLaw c w p) = _
    rw [← Measure.map_map hqa (mixedArrayRegroup I (Fin n) J).measurable, mixedScalarArrayLaw_regroup c w hw p]
    rw [Measure.pi_map_pi
      (μ := fun j : J => mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun i => p i j))
      (f := fun _ : J => q) (hμ := houtput) (fun _ => hq.aemeasurable)]
    simp_rw [show ∀ j, Measure.map q (mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun i => p i j)) =
      realDensityMeasure μ (f j) from hflaw]
    exact realDensityMeasure_pi (fun _ : J => μ) f hfi (fun j y => (hfB j y).1)
  · intro x hx
    change (∏ j, f j (normalizedLatticeQuotient W b hb (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)))) = _
    simp_rw [hfval _ _ (hx _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule Set
open scoped BigOperators

noncomputable def constantChartDistortion (n : ℕ) : ℝ := Real.exp (20 * ((n : ℝ) + 1) ^ 3)

noncomputable def constantChartWidth (a n : ℕ) : ℝ :=
  1 / (8 * constantChartDistortion n * ((a : ℝ) + 1))

theorem constantChartWidth_pos (a n : ℕ) : 0 < constantChartWidth a n := by
  unfold constantChartWidth constantChartDistortion
  positivity

theorem constantChartWidth_small (a n : ℕ) :
    constantChartDistortion n * ((a : ℝ) + 1) * constantChartWidth a n ≤ 1 / 4 := by
  have hC : constantChartDistortion n ≠ 0 := Real.exp_ne_zero _
  have ha : (a : ℝ) + 1 ≠ 0 := by positivity
  calc
    constantChartDistortion n * ((a : ℝ) + 1) * constantChartWidth a n = 1 / 8 := by
      unfold constantChartWidth
      field_simp [hC, ha]
    _ ≤ 1 / 4 := by norm_num

noncomputable def constantChartDensityCap (a n : ℕ) : ℝ :=
  constantChartDistortion n * (constantChartWidth a n)⁻¹ ^ a *
    (8 * (probabilityProfileLipschitz : ℝ) / constantChartWidth a n) ^ n

theorem constantChartDensityCap_nonneg (a n : ℕ) : 0 ≤ constantChartDensityCap a n := by
  unfold constantChartDensityCap constantChartDistortion
  have hR := constantChartWidth_pos a n
  positivity

theorem exists_uniform_constant_quotient_density {D I : Type*} [Fintype D] [Fintype I]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (e : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
    let a := Fintype.card I
    let n := finrank ℝ Wᗮ
    let R := constantChartWidth a n
    ∃ (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
      (F : (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ),
      Measurable F ∧ (∀ y, 0 ≤ F y ∧ F y ≤ constantChartDensityCap a n) ∧
      Integrable F μ ∧ (∫ y, F y ∂μ) = 1 ∧
      Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart e x))
        (mixedCoefficientLaw (fun _ => 0) (fun _ => R)
          (latticeConstantMass W b (fun _ => R) (fun _ => constantChartWidth_pos a n))) =
        realDensityMeasure μ F ∧
      ∀ x, mixedCoefficientDensity (fun _ => 0) (fun _ => R)
          (latticeConstantMass W b (fun _ => R) (fun _ => constantChartWidth_pos a n)) x ≠ 0 →
        F (normalizedLatticeQuotient W b hb (orthonormalMixedChart e x)) =
          ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
            mixedCoefficientDensity (fun _ => 0) (fun _ => R)
              (latticeConstantMass W b (fun _ => R) (fun _ => constantChartWidth_pos a n)) x := by
  dsimp only
  let a := Fintype.card I
  let n := finrank ℝ Wᗮ
  let C := constantChartDistortion n
  let R := constantChartWidth a n
  have hR : 0 < R := constantChartWidth_pos a n
  have hC : 0 < C := Real.exp_pos _
  obtain ⟨b, hb, _, _, hi, _, hv⟩ := exists_quantitative_projected_chart W
  have hvol : ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) ≤
      C * ∏ j, (basisAxisScale b j : ℝ) :=
    (div_le_iff₀ (Finset.prod_pos (fun j _ => basisAxisScale_cast_pos b j))).mp hv
  obtain ⟨F, hFm, hFB, hFi, hFmass, hFlaw, hFvalue⟩ := constantCoefficient_quotient_density W b hb e μ
    (fun _ => R) (fun _ => hR) (fun _ => R) (fun _ => hR) hC.le hR.le hC.le hi
    (fun _ => le_rfl) (fun _ => le_rfl) (constantChartWidth_small a n) hvol
  refine ⟨b, hb, F, hFm, ?_, hFi, hFmass, hFlaw, hFvalue⟩
  intro y
  simpa only [profileWidthFactor, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    constantChartDensityCap] using hFB y

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule

theorem scaledCoefficientDensity_product_law {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    realDensityMeasure volume (scaledCoefficientDensity e T c w) =
      Measure.pi (fun j => affineCoefficientMeasure (c j / monomialScale T (e j))
        (w j / monomialScale T (e j))) := by
  symm
  exact independentCoordinateDensity_measure
    (fun j => affineProbabilityProfile (c j / monomialScale T (e j)) (w j / monomialScale T (e j)))
    (fun j => affineProbabilityProfile_integrable _ (div_pos (hw j) (monomialScale_pos T hT (e j))))
    (fun j => affineProbabilityProfile_nonneg _ (div_pos (hw j) (monomialScale_pos T hT (e j))))
    (fun j => affineProbabilityProfile_integral _ (div_pos (hw j) (monomialScale_pos T hT (e j))))

theorem scaledArrayLaw_rows {I J V : Type*} [Fintype I] [Fintype J] {n : ℕ}
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ) :
    independentPolynomialLaw
      (fun i => realDensityMeasure volume (scaledCoefficientDensity e T (c i) (w i)))
      (fun i => Measure.pi (fun j => (p i j).toMeasure)) =
    mixedScalarArrayLaw (fun i j => c i j / monomialScale T (e j))
      (fun i j => w i j / monomialScale T (e j)) p := by
  unfold independentPolynomialLaw mixedScalarArrayLaw
  simp_rw [scaledCoefficientDensity_product_law e T hT _ _ (hw _)]

theorem scaledProfile_div_bound {c w S R : ℝ} (hw : 0 ≤ w) (hS : 1 ≤ S) (hb : |c| + w ≤ R) :
    |c / S| + w / S ≤ R := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  rw [abs_div, abs_of_pos hS0, ← add_div]
  apply (div_le_self (add_nonneg (abs_nonneg _) hw) hS).trans hb

theorem scaledAbs_le_of_bound {a S R : ℝ} (hS : 1 ≤ S) (hb : |a| * S ≤ R) : |a| ≤ R := by
  calc
    |a| = |a| * 1 := (mul_one _).symm
    _ ≤ |a| * S := mul_le_mul_of_nonneg_left hS (abs_nonneg a)
    _ ≤ R := hb

theorem scaledArray_quotient_density {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 1 ≤ T v)
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (hcw : ∀ i j, |c i j| + w i j ≤ R)
    (hp : ∀ i j k, k ∈ (p i j).support →
      |(k : ℝ) / basisAxisScale b i| * monomialScale T (e j) ≤ R) :
    ∃ F : (J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ,
      Measurable F ∧ (∀ y, 0 ≤ F y) ∧ Integrable F (Measure.pi (fun _ : J => μ)) ∧
      (∫ y, F y ∂Measure.pi (fun _ : J => μ)) = 1 ∧
      Measure.map (mixedArrayQuotient W b hb o)
        (independentPolynomialLaw
          (fun i => realDensityMeasure volume (scaledCoefficientDensity e T (c i) (w i)))
          (fun i => Measure.pi (fun j => (p i j).toMeasure))) =
        realDensityMeasure (Measure.pi (fun _ : J => μ)) F := by
  have hT0 : ∀ v, 0 < T v := fun v => lt_of_lt_of_le zero_lt_one (hT v)
  obtain ⟨F, hFm, hFB, hFi, hF1, hFlaw, _⟩ := mixedArray_quotient_density W b hb o μ
    (fun i j => c i j / monomialScale T (e j)) (fun i j => w i j / monomialScale T (e j))
    (fun i j => div_pos (hw i j) (monomialScale_pos T hT0 (e j))) p hC hR hchart hsmall
    (fun i j => scaledProfile_div_bound (hw i j).le (one_le_monomialScale T hT (e j)) (hcw i j))
    (fun i j k hk => scaledAbs_le_of_bound (one_le_monomialScale T hT (e j)) (hp i j k hk))
  refine ⟨F, hFm, fun y => (hFB y).1, hFi, hF1, ?_⟩
  rw [scaledArrayLaw_rows e T hT0 c w hw p]
  exact hFlaw

end Erdos3

end

end OAI
