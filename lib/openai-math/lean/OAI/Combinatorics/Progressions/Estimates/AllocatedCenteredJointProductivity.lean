import OAI.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

attribute [local irreducible] selectedJointFiniteLaw selectedJointReference selectedResidueFiniteLaw

theorem selectedJointFiniteLaw_integral_productivity
    {C B K I R Y : Type*} [MeasurableSpace C] [Fintype K] [Fintype I] [Fintype R]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (sites : FiniteProbabilityWeights R)
    (image : B → (K × I → ℤ) → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hmarginal : ∀ r,
      let F := fun c => (selectedJointFiniteLaw A hA modulus T W hW hZ (D c)
        (hD0 c) (hD c)).complexMean (fun z => (test (image z.1.val z.2.val r) : ℂ))
      Integrable F μ ∧ ‖(∫ c, F c ∂μ) - (parent : ℂ)‖ ≤ η)
    (hcollision : ∀ c,
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => noninjectivityIndicator (image z.1.val z.2.val)) ≤ σ / 16) :
    σ / 4 ≤ ∫ c,
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mass
        (Finset.univ.filter (fun z => Function.Injective (image z.1.val z.2.val) ∧
          σ / 2 ≤ sites.mean (fun r => test (image z.1.val z.2.val r)))) ∂μ := by
  let law := fun c => selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)
  let sampledImage := fun (z : A × rectangularWeightIndices 0 W 1) r => image z.1.val z.2.val r
  have hi (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1) :
      Integrable (fun c => (law c).mean (fun z => f z.1.val z.2.val)) μ :=
    selectedJointFiniteLaw_realTest_integrable A hA modulus T W hW hZ μ D hDm hD0 hD f hf
  have hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (sampledImage z))) μ := by
    apply hi (fun a z => noninjectivityIndicator (image a z))
    intro a z
    simp only [noninjectivityIndicator]
    split_ifs <;> norm_num
  have hiProd : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (sampledImage z) ∧ σ / 2 ≤
        sites.mean (fun r => test (sampledImage z r))))) μ := by
    simp only [← FiniteProbabilityWeights.mean_indicator, Finset.mem_filter,
      Finset.mem_univ, true_and]
    apply hi (fun a z => if Function.Injective (image a z) ∧
      σ / 2 ≤ sites.mean (fun r => test (image a z r)) then 1 else 0)
    intro a z
    split_ifs <;> norm_num
  have hbadmean : (∫ c, (law c).mean
      (fun z => noninjectivityIndicator (sampledImage z)) ∂μ) ≤ σ / 16 := by
    have h := integral_mono hiBad (integrable_const (σ / 16)) hcollision
    simpa only [integral_const, probReal_univ, one_smul] using h
  exact integral_productive_injective_mass_of_complex_marginals μ law sites sampledImage test
    hσ hη hparent htest (fun r => (hmarginal r).1) (fun r => (hmarginal r).2)
    hiBad hiProd hbadmean

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X Sites : Type*} [Fintype G] [Fintype X] [Fintype Sites] [Nonempty Sites]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

theorem allocatedCenteredJoint_productivity
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (widths : Option (LayerSamplerVariables G I n B) × X → ℝ)
    (hwidths : ∀ z, 0 < widths z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center))
    (site : Sites → LayerSamplerVariables G I n B → ℤ)
    (test : (X → ℤ) → ℝ) {gain error parent : ℝ}
    (hgain : 0 < gain) (herror : error ≤ gain / 8) (hparent : gain ≤ parent)
    (htest : ∀ y, test y ≤ 1) :
    let density := allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem
    let law := fun center => selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass
      (density center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) (hD center)
    (∀ q, Integrable (fun center => (law center).complexMean
      (fun z => (test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) : ℂ))) μ ∧
      ‖(∫ center, (law center).complexMean
        (fun z => (test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) : ℂ)) ∂μ) -
          (parent : ℂ)‖ ≤ error) →
    (∀ center, (law center).mean
      (fun z => noninjectivityIndicator (fun q => jointIntegerPhysicalSite (site q)
        (z.1.val,z.2.val))) ≤ gain / 16) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U b hb o hR hσ S poly hmem c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) := by
  intro density law hmarginal hcollision productive joint
  have hDm (a : X → ℤ) z : Measurable (fun center => density center a z) :=
    allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hmem a z
  have hD0 := allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem
  have hp := selectedJointFiniteLaw_integral_productivity bases hbases stride cells widths
    hwidths hmass μ density hDm hD0 hD (FiniteProbabilityWeights.uniform Sites)
    (fun a z q => jointIntegerPhysicalSite (site q) (a,z)) test
    hgain herror hparent htest hmarginal hcollision
  have hp' : gain / 4 ≤ ∫ center, (law center).mass productive ∂μ := by
    simpa only [FiniteProbabilityWeights.uniform_mean] using hp
  have hweight z : Measurable (fun center => (law center).weight z) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells widths hwidths hmass
      density hDm hD0 hD z
  apply centeredFiniteProbabilityMeasure_productive_family μ law hweight productive _ _ hp'
  intro center z hz
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  refine ⟨c, hc, ?_⟩
  have hd := (selectedJointFiniteLaw_support bases hbases stride cells widths hwidths hmass
    (density center) (hD0 center) (hD center) z hz).2
  change 0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem
    center z.1.val z.2.val at hd
  rw [allocatedCenteredJointDensity_eq_affine B U b hb o hR hσ S poly hmem center c hc] at hd
  exact hd.ne'

end Erdos3.VectorPolynomial

end

end OAI
