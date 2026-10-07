import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource
import OAI.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
import OAI.Combinatorics.Progressions.Linear.JointFrameCoefficientCoverSample

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem reweightPositive_weight_measurable {X C : Type*} [Fintype X]
    [MeasurableSpace C] (p : FiniteProbabilityWeights X)
    (D : C → X → ℝ) (hDm : ∀ x, Measurable (fun c => D c x))
    (hD0 : ∀ c x, 0 ≤ D c x) (hD : ∀ c, 0 < p.mean (D c)) (x : X) :
    Measurable (fun c => (p.reweightPositive (D c) (hD0 c) (hD c)).weight x) := by
  simp only [reweightPositive_weight]
  exact ((hDm x).const_mul (p.weight x)).div (p.mean_measurable D hDm)

end FiniteProbabilityWeights

section Joint

variable {C B K I : Type*} [MeasurableSpace C] [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

include hA hW hZ in

theorem selectedJointDensityMass_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z)) :
    Measurable (fun c => selectedJointDensityMass A modulus T W (D c)) := by
  have h := (selectedJointReference A hA modulus T W hW hZ).mean_measurable
    (fun c z => D c z.1.val z.2.val) (fun z => hDm z.1.val z.2.val)
  simpa only [selectedJointReference_densityMass] using h

theorem selectedJointFiniteLaw_weight_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (z : A × rectangularWeightIndices 0 W 1) :
    Measurable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).weight z) := by
  simp only [selectedJointFiniteLaw_weight]
  exact ((hDm z.1.val z.2.val).const_mul _).div
    (selectedJointDensityMass_measurable A hA modulus T W hW hZ D hDm)

theorem selectedJointFiniteLaw_realTest_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (f : B → (K × I → ℤ) → ℝ) :
    Measurable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => f z.1.val z.2.val)) :=
  Finset.measurable_sum _ (fun z _ =>
    (selectedJointFiniteLaw_weight_measurable A hA modulus T W hW hZ D hDm hD0 hD z).mul_const _)

theorem selectedJointFiniteLaw_realTest_integrable
    (μ : Measure C) [IsFiniteMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1) :
    Integrable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => f z.1.val z.2.val)) μ := by
  apply Integrable.of_bound
    (selectedJointFiniteLaw_realTest_measurable A hA modulus T W hW hZ D hDm hD0 hD f).aestronglyMeasurable 1
  apply ae_of_all
  intro c
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ((selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean_mem_Icc
    (fun z => f z.1.val z.2.val) (fun z => abs_le.mp (hf z.1.val z.2.val)))

end Joint

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

omit [Fintype X] in

theorem jointSelectedPhysicalDensity_measurable_center
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (a : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    Measurable (fun center =>
      jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm center a z) :=
  (translatedSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀
    (fun j => translate (fun i => (a i : ℝ)) (p j))
    (fun j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)) z).comp
      (coefficientConstantCenter_continuous U).measurable

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

noncomputable def allocatedJointBaseDensity (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S (affineSampleCoefficientTorus U
    (fun j => translate (fun t => (base t : ℝ)) (poly j))
    (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (poly j) (hmem j))
    (fun k t => (z (k, t) : ℝ)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype X] in
theorem allocatedJointBaseDensity_nonneg (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem base z :=
  canonicalCoefficientDensity_nonneg U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S)
    (allocatedLayerWidths_pos B U b hR hσ S) _

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem
local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

noncomputable def allocatedOriginalJointLaw :
    FiniteProbabilityWeights
      (PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) ×
        (bases × rectangularWeightIndices 0 widths 1)) :=
  selectedJointTupleLaw bases hbases stride cells widths hwidths hmass baseDensity
    (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal whole

omit [DecidableEq G] in
theorem allocatedOriginalJointLaw_source (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (allocatedOriginalJointLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass
      bases hbases htotal).complexMean
        (fun z => test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
          (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val)) =
      𝔼 base ∈ bases, allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
        base cells hmass test (selectedJointDensityMass bases stride cells widths baseDensity) poly hmem := by
  exact selectedJointTupleLaw_complexMean bases hbases stride cells widths hwidths hmass baseDensity
    (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal whole
    (fun y base z => test (physicalCubeRootDifferences
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U b S x y) base z))

include hbases htotal in
omit [DecidableEq G] in
theorem allocatedOriginalSource_base_average_bound (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1) :
    ‖𝔼 base ∈ bases, allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
      base cells hmass test (selectedJointDensityMass bases stride cells widths baseDensity) poly hmem‖ ≤ 1 := by
  rw [← allocatedOriginalJointLaw_source B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
    hmass bases hbases htotal x test]
  let law := allocatedOriginalJointLaw (dim := dim) B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
    stride cells hmass bases hbases htotal
  apply (law.norm_complexMean_le_mean_norm _).trans
  exact (law.mean_mono (fun z => htest _)).trans_eq (law.mean_const 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem
local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

noncomputable def allocatedOriginalPathLaw :
    FiniteProbabilityWeights (bases × rectangularWeightIndices 0 widths 1) :=
  selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass baseDensity
    (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin dim) S.value S.positive)

theorem allocatedOriginalPathLaw_cube_source
    (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
      hmass bases hbases htotal).complexMean (fun z =>
        𝔼 cube : SupportedCube dim (integerBox sides : Set (LayerSamplerVariables G I n B → ℤ)),
          test (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) =
      (kernelLaw).complexMean (fun x =>
        𝔼 base ∈ bases, allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
          base cells hmass test (selectedJointDensityMass bases stride cells widths baseDensity) poly hmem) := by
  let law := allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
    stride cells hmass bases hbases htotal
  let value := fun (z : bases × rectangularWeightIndices 0 widths 1)
      (x : G → IntegerScalarCubeBox (Fin dim) S.value)
      (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)) =>
    test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val)
  calc
    _ = law.complexMean (fun z => (kernelLaw).complexMean (fun x => (whole).complexMean (value z x))) := by
      apply congrArg law.complexMean
      funext z
      refine (integerBox_cube_mean_split S.value S.positive
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S) dim
        (fun cube => test (physicalCubeRootDifferences cube.2 cube.1 z.1.val z.2.val))).trans ?_
      apply congrArg (kernelLaw).complexMean
      funext x
      apply congrArg (whole).complexMean
      funext y
      have hroot : allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y =
          Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) := by
        funext k
        exact zero_add _
      dsimp only [value]
      rw [hroot]
      rfl
    _ = (kernelLaw).complexMean (fun x => law.complexMean (fun z => (whole).complexMean (value z x))) :=
      FiniteProbabilityWeights.complexMean_commute law (kernelLaw) _
    _ = (kernelLaw).complexMean (fun x => (whole).complexMean (fun y => law.complexMean (fun z => value z x y))) := by
      apply congrArg (kernelLaw).complexMean
      funext x
      exact FiniteProbabilityWeights.complexMean_commute law (whole) _
    _ = _ := by
      apply congrArg (kernelLaw).complexMean
      funext x
      have h := allocatedOriginalJointLaw_source B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
        stride cells hmass bases hbases htotal x test
      simpa only [allocatedOriginalJointLaw, selectedJointTupleLaw,
        FiniteProbabilityWeights.complexMean_prod, law, allocatedOriginalPathLaw, value] using h

theorem allocatedOriginalPathLaw_self_cube_source (f : (X → ℤ) → ℂ) :
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
      hmass bases hbases htotal).complexMean (fun z =>
        normalizedSupportedCubeSum dim (integerBox sides)
          (fun _ t => f (jointIntegerPhysicalSite t (z.1.val, z.2.val)))) =
      (kernelLaw).complexMean (fun x =>
        𝔼 base ∈ bases, allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
          base cells hmass (physicalCubeSiteTest (integerSelfSiteTest dim f))
          (selectedJointDensityMass bases stride cells widths baseDensity) poly hmem) := by
  calc
    _ = (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
        hmass bases hbases htotal).complexMean (fun z =>
        𝔼 cube : SupportedCube dim (integerBox sides : Set (LayerSamplerVariables G I n B → ℤ)),
          physicalCubeSiteTest (integerSelfSiteTest dim f)
            (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) := by
      congr 1
      funext z
      exact normalizedSupportedCubeSum_joint dim (integerBox sides) f z.1.val z.2.val
    _ = _ := allocatedOriginalPathLaw_cube_source B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
      stride cells hmass bases hbases htotal (physicalCubeSiteTest (integerSelfSiteTest dim f))

theorem allocatedOriginalPathLaw_finite_self_cube_source
    {T : Type*} [Nonempty T] (e : T → LayerSamplerVariables G I n B → ℤ)
    (he : Function.Injective e)
    (hcover : ∀ t ∈ integerBox sides, ∃ u, e u = t) (f : (X → ℤ) → ℂ) :
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
      hmass bases hbases htotal).complexMean (fun z =>
        normalizedSupportedCubeSum dim (integerBox sides)
          (fun _ t => finiteSiteExtension e
            (fun u => f (jointIntegerPhysicalSite (e u) (z.1.val, z.2.val))) t)) =
      (kernelLaw).complexMean (fun x =>
        𝔼 base ∈ bases, allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ
          base cells hmass (physicalCubeSiteTest (integerSelfSiteTest dim f))
          (selectedJointDensityMass bases stride cells widths baseDensity) poly hmem) := by
  calc
    _ = (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
        hmass bases hbases htotal).complexMean (fun z =>
        normalizedSupportedCubeSum dim (integerBox sides)
          (fun _ t => f (jointIntegerPhysicalSite t (z.1.val, z.2.val)))) := by
      apply congrArg (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases hbases htotal).complexMean
      funext z
      exact normalizedSupportedCubeSum_finiteSiteExtension dim (integerBox sides) e he hcover
        (fun t => f (jointIntegerPhysicalSite t (z.1.val, z.2.val)))
    _ = _ := allocatedOriginalPathLaw_self_cube_source B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal f

noncomputable def allocatedSlicedCubeSource
    (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
    (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ) (f : (X → ℤ) → ℂ) : ℂ :=
  (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))).complexMean
    (fun cube =>
      (𝔼 base ∈ bases, ∑' z,
        ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest dim f)
            (physicalCubeRootDifferences
              (commonStridePoint c step (fun k => (cube k none : ℤ)))
              (fun j k => (step : ℤ) * (cube k (some j) : ℤ)) base z) *
            (baseDensity base z : ℂ))) / (selectedJointDensityMass bases stride cells widths baseDensity : ℂ))

theorem allocatedOriginalPathLaw_sliced_cube_source
    (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
    (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ) (f : (X → ℤ) → ℂ) :
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
      hmass bases hbases htotal).complexMean (fun z =>
        normalizedSupportedCubeSum dim (integerBox H)
          (fun _ t => f (jointIntegerPhysicalSite (commonStridePoint c step t) (z.1.val, z.2.val)))) =
      allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass
        bases H hH c step f := by
  let law := allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
    stride cells hmass bases hbases htotal
  let cubeLaw := FiniteProbabilityWeights.pi
    (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))
  let value := fun (cube : ∀ k, IntegerScalarCubeBox (Fin dim) (H k)) (base : X → ℤ)
      (z : Option (LayerSamplerVariables G I n B) × X → ℤ) =>
    physicalCubeSiteTest (integerSelfSiteTest dim f)
      (physicalCubeRootDifferences (commonStridePoint c step (fun k => (cube k none : ℤ)))
        (fun j k => (step : ℤ) * (cube k (some j) : ℤ)) base z)
  calc
    _ = law.complexMean (fun z => cubeLaw.complexMean (fun cube => value cube z.1.val z.2.val)) := by
      apply congrArg law.complexMean
      funext z
      exact commonStride_normalized_cube_source dim H hH c step f z.1.val z.2.val
    _ = cubeLaw.complexMean (fun cube => law.complexMean (fun z => value cube z.1.val z.2.val)) :=
      FiniteProbabilityWeights.complexMean_commute law cubeLaw _
    _ = _ := by
      apply congrArg cubeLaw.complexMean
      funext cube
      exact selectedJointFiniteLaw_weighted_expectation bases hbases stride cells widths hwidths hmass
        baseDensity (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal (value cube)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j) (c : ∀ j, U j)

omit [DecidableEq G] [Fintype X] [∀ index, DecidableEq (I index)]
  [∀ axis, DecidableEq (B axis)] in
theorem allocatedJointBaseDensity_subtractConstant_affine (a : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedJointBaseDensity B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) a z =
      allocatedAffineDensity B U b hb o hR hσ S poly hmem c
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)) := by
  unfold allocatedJointBaseDensity
  rw [affineSampleCoefficientTorus_joint_frame U
    (fun j => subtractConstant (c j).val (poly j))
    (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) a z,
    affineSampleCoefficientTorus_subtractConstant U poly hmem c]
  rfl

omit [DecidableEq G] [Fintype X] [∀ index, DecidableEq (I index)]
  [∀ axis, DecidableEq (B axis)] in
theorem allocatedJointBaseDensity_subtractConstant_selected (L₀ : ℕ)
    (hS : S = selectedLayerSamplerScale B U b R σ hR hσ L₀)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1)))) :
    allocatedJointBaseDensity B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) =
      jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center := by
  funext a z
  exact allocatedJointDensity_subtractConstant B U b hb o R σ hR hσ L₀
    S hS poly hmem center c hc a z

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X
    (fun j => subtractConstant (c j).val (poly j))
    (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))))

omit [DecidableEq G] [∀ index, DecidableEq (I index)]
  [∀ axis, DecidableEq (B axis)] in
theorem allocatedOriginalPathLaw_positive_affine
    (z : bases × rectangularWeightIndices 0 widths 1)
    (hz : 0 < (allocatedOriginalPathLaw B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
      N hN hW hτ hξ stride cells hmass bases hbases htotal).weight z) :
    allocatedAffineDensity B U b hb o hR hσ S poly hmem c
      (fun k i => (jointIntegerFrame (z.1.val, z.2.val) k i : ℝ)) ≠ 0 := by
  have h := (selectedJointFiniteLaw_support bases hbases stride cells widths
    (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
    (allocatedJointBaseDensity B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)))
    (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))) htotal z hz).2
  rw [allocatedJointBaseDensity_subtractConstant_affine B U b hb o hR hσ S poly hmem c] at h
  exact h.ne'

omit [DecidableEq G] [∀ index, DecidableEq (I index)]
  [∀ axis, DecidableEq (B axis)] in
theorem allocatedOriginalPathLaw_subtractConstant_eq_selected (L₀ : ℕ)
    (hS : S = selectedLayerSamplerScale B U b R σ hR hσ L₀)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (hselected : 0 < selectedJointDensityMass bases stride cells widths
      (jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center)) :
    allocatedOriginalPathLaw B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
      N hN hW hτ hξ stride cells hmass bases hbases htotal =
      selectedJointFiniteLaw bases hbases stride cells widths
        (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
        (jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center)
        (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hmem center) hselected := by
  unfold allocatedOriginalPathLaw
  simp only [allocatedJointBaseDensity_subtractConstant_selected B U b hb o hR hσ S poly hmem c L₀ hS center hc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
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

noncomputable def allocatedCenteredJointDensity
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S
    (coefficientConstantCenter U center +
      affineSampleCoefficientTorus U poly hmem
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)))

omit [Fintype X] in
theorem allocatedCenteredJointDensity_eq_affine
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z =
      allocatedAffineDensity B U b hb o hR hσ S poly hmem c
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)) := by
  unfold allocatedCenteredJointDensity allocatedAffineDensity
  rw [centeredAffineCoefficientTorus_eq_subtractive, ← hc]

omit [Fintype X] in
theorem allocatedJointBaseDensity_subtractConstant_centered
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1)))) :
    allocatedJointBaseDensity B U b hb o hR hσ S X
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) =
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center := by
  funext a z
  rw [allocatedJointBaseDensity_subtractConstant_affine,
    allocatedCenteredJointDensity_eq_affine B U b hb o hR hσ S poly hmem center c hc]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype X] in
theorem allocatedCenteredJointDensity_nonneg
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z :=
  canonicalCoefficientDensity_nonneg U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S)
    (allocatedLayerWidths_pos B U b hR hσ S) _

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

omit [Fintype X] [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCenteredJointDensity_measurable_center
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    Measurable (fun center =>
      allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z) :=
  (canonicalCoefficientDensity_measurable U b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S)).comp
      ((coefficientConstantCenter_continuous U).measurable.add measurable_const)

variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

omit [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem allocatedOriginalPathLaw_subtractConstant_eq_centered
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))))
    (hcenter : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)) :
    allocatedOriginalPathLaw B U b hb o hR hσ S X
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
      N hN hW hτ hξ stride cells hmass bases hbases htotal =
    selectedJointFiniteLaw bases hbases stride cells widths
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hcenter := by
  unfold allocatedOriginalPathLaw
  simp only [allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

variable {X : Type*}
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
variable (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)

include hC hV hσ1 hCinv hchart hsmall in

theorem allocatedCenteredJointDensity_cap :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z ≤
      (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
  exact (allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall _).2

include hC hV hσ1 hCinv hchart hsmall in

theorem allocatedCenteredJointDensity_fixedScale_le_exp
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    : allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z ≤
      Real.exp (allocatedFourierLogBudget m P) := by
  exact allocatedCoefficientDensity_fixedScale_le_exp B U b hb o hR hσ S C V
    hC hV hσ1 Cinv hCinv hchart hsmall hP hm hK hRP hσP hcount hI hn hJ
    hAP hSP hCP hVP _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocatedFixedScale_center_mixture_compare
    {m : ℕ} {X G : Type*} [Fintype X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hσ1 : ∀ j, σ j ≤ 1) (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
    (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ)
    (hlocal : ∀ center, 0 < selectedResidueDensityMass stride T W
      (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base))
    {P : ℝ}
    (hclose : ∀ center, |selectedResidueDensityMass stride T W
      (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base) - 1| ≤
        3 * positiveProjectionAccuracy P)
    (hcomparison : ∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (φ : (X → ℝ) → ℂ), (∀ v, ‖φ v‖ ≤ 1) →
      let sample := fun z => affineSampleCoefficientTorus U p hm
        (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
      let D₀ := allocatedCoefficientDensity B U b hb o hR hσ S
      let fiber := fun z => coefficientFiberAverage U μ root
        (fun x => D₀ (coefficientConstantCenter U center + x))
        (coefficientEvaluationTorus U root (sample z))
      ‖(∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
        (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
          (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base z : ℂ))) -
        (∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) * (fiber z : ℂ)))‖ ≤
        3 * positiveProjectionAccuracy P) :
    ∀ ψ : (X → ℝ) → ℂ, (∀ v, ‖ψ v‖ ≤ 1) →
      ‖(∫ center, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ
          (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base)
          (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
          (hlocal center) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
        ∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          ψ (physicalAffineSite root z)‖ ≤ 6 * positiveProjectionAccuracy P := by
  intro ψ hψ
  let D₀ := allocatedCoefficientDensity B U b hb o hR hσ S
  have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hcap := allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall
  have hbound (x) : ‖D₀ x‖ ≤
      (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcap x).1]
    exact (hcap x).2
  let D := fun center => allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base
  let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
    affineSampleCoefficientTorus U p hm
    (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
  let F := fun center z => coefficientFiberAverage U μ root
    (fun x => D₀ (coefficientConstantCenter U center + x))
    (coefficientEvaluationTorus U root (sample z))
  apply selectedResidue_center_mixture_compare μ stride T W hW hZ D
    (fun z => allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S p hm base z)
    (fun center => allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
    hlocal F
    (fun z => coefficientMixedFiber_integrable U μ D₀ hspec.1 hbound root _)
    (fun z => (coefficientMixedFiber_average U μ D₀ hspec.1 hbound root _).trans hspec.2.2.2.1)
    (fun z => ψ (physicalAffineSite root z)) (fun _ => hψ _)
  intro center
  have hraw := hcomparison center (fun v => ψ (v - (fun i => (base i : ℝ))))
    (fun _ => hψ _)
  dsimp only at hraw
  simp only [add_sub_cancel_left] at hraw
  have herr := selectedResidueDensityPMF_error_of_bounded_test stride T W hW hZ (D center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
    (hlocal center) (fun z => ψ (physicalAffineSite root z)) (fun _ => hψ _) hraw (hclose center)
  exact herr.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
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

omit [Fintype X] [∀ j, Fintype (J j)] in
theorem preparedModularGeneralCentered_degree
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) (c : ∀ j, U j) :
    ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (subtractConstant (c j).val (poly j)) :=
  fun j => (hp j).subtractConstant (c j).val

omit [Fintype X] in
theorem preparedModularGeneralCentered_rank (T : X → ℝ) (rank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) T rank (U j) (poly j)) (c : ∀ j, U j) :
    ∀ j, HasLayerSamplingRank (j.val + 1) T rank (U j)
      (subtractConstant (c j).val (poly j)) :=
  fun j => (hasLayerSamplingRank_subtractConstant_iff (Nat.succ_pos j.val)
    T rank (U j) (c j).val (poly j)).mpr (hrank j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

omit [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem preparedModularGeneralCenteredLaw
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (hcenter : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)) :
    ∃ htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))),
      allocatedOriginalPathLaw B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
        N hN hW hτ hξ stride cells hmass bases hbases htotal =
      selectedJointFiniteLaw bases hbases stride cells widths
        (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
        (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
        (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hcenter := by
  have htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))) := by
    rw [allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc]
    exact hcenter
  exact ⟨htotal, allocatedOriginalPathLaw_subtractConstant_eq_centered B U b hb o hR hσ S
    poly hmem N hN hW hτ hξ stride cells hmass bases hbases center c hc htotal hcenter⟩

end Erdos3.VectorPolynomial

end

end OAI
