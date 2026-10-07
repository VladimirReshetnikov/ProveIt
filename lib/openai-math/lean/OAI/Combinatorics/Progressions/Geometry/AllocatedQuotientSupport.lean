import OAI.Combinatorics.Progressions.Estimates.AllocatedShortAxis

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL
local notation "source" => allocatedMixedArrayLaw W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL Pc

noncomputable def allocatedQuotientDensity :
    (J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ :=
  canonicalArrayDensity W b hb o (allocatedArrayCenters e T Pc R)
    (allocatedArrayWidths e T Pc j₀ R σ) intLaws

local notation "density" => allocatedQuotientDensity W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL Pc hb o

theorem allocatedQuotientDensity_measurable : Measurable density :=
  canonicalArrayDensity_measurable W b hb o _ _ _

theorem allocatedQuotientDensity_spec
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4) :
    Measurable density ∧ (∀ y, 0 ≤ density y) ∧ Integrable density (Measure.pi (fun _ : J => μ)) ∧
      (∫ y, density y ∂Measure.pi (fun _ : J => μ)) = 1 ∧
      Measure.map (mixedArrayQuotient W b hb o) source = realDensityMeasure (Measure.pi (fun _ : J => μ)) density := by
  have hT0 : ∀ v, 0 < T v := fun v => lt_of_lt_of_le zero_lt_one (hT v)
  have hw := allocatedArrayWidths_pos e T hT0 Pc j₀ hR hσ
  have hs := allocatedArrayColumns_chart W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ
    hgap hεL Pc o hc₀ hz₀ he₀ hσ1 hprincipal hC hchart hsmall
  have hm := canonicalArrayDensity_mass W b hb o μ (allocatedArrayCenters e T Pc R)
    (allocatedArrayWidths e T Pc j₀ R σ) hw intLaws hs
  refine ⟨canonicalArrayDensity_measurable W b hb o _ _ _,
    canonicalArrayDensity_nonneg W b hb o _ _ hw _, hm.1, hm.2, ?_⟩
  unfold allocatedMixedArrayLaw
  rw [allocatedArrayLaw_rows e T hT0 Pc j₀ hR hσ intLaws]
  exact canonicalArrayDensity_law W b hb o μ _ _ hw intLaws hs

theorem allocatedQuotientDensity_recover
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    {y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup} (hy : density y ≠ 0) :
    ∃! a : (I → J → ℝ) × (Fin n → J → ℤ),
      (mixedArrayQuotient W b hb o a = y ∧ mixedArrayInChart W b o a ∧
        mixedArraySupported (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) intLaws a) ∧
      ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) → mixedPolynomialPoint W b o e a.1 a.2 x ∈ standardLatticeSmallBox D := by
  obtain ⟨a, ha, hu⟩ := canonicalArrayDensity_recover_unique W b hb o
    (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) intLaws hy
  refine ⟨a, ⟨ha, ?_⟩, fun z hz => hu z hz.1⟩
  exact allocatedArraySupported_polynomial_chart W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ
    hgap hεL Pc o hc₀ hz₀ he₀ hσ1 hprincipal hC hchart hsmall a ha.2.2

theorem allocatedQuotientDensity_nonzero_iff
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    density y ≠ 0 ↔ ∃ a : (I → J → ℝ) × (Fin n → J → ℤ),
      (mixedArrayQuotient W b hb o a = y ∧ mixedArrayInChart W b o a ∧
        mixedArraySupported (allocatedArrayCenters e T Pc R) (allocatedArrayWidths e T Pc j₀ R σ) intLaws a) ∧
      ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) → mixedPolynomialPoint W b o e a.1 a.2 x ∈ standardLatticeSmallBox D := by
  constructor
  · intro hy
    exact (allocatedQuotientDensity_recover W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ
      hgap hεL Pc hb o hc₀ hz₀ he₀ hσ1 hprincipal hC hchart hsmall hy).exists
  · rintro ⟨a, ha, _⟩
    exact (canonicalArrayDensity_nonzero_iff W b hb o _ _ intLaws y).mpr ⟨a, ha⟩

end Erdos3

end

end OAI
