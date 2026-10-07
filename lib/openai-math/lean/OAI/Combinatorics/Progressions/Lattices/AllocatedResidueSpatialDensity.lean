import OAI.Combinatorics.Progressions.Probability.AllocatedPrescribedRefinedDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "rootAt" => (fun w => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
local notation "dirsAt" => (fun w => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w))
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (g : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w)) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

include hσ1 hC hchart hsmall hg hg0 hlaw in
theorem allocatedResidue_spatial_density_comparison
    (M : ℕ) (hM : 0 < M)
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
    (hsize : ∀ t, (Fintype.card α + 1) * M ≤ principalAxisLength (fun a => ¬grid a) sides t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : principalResidueLabel M v₀ = label)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod M))
    {ε : ℝ} (hpoint : ∀ z, |(allocatedLongResidueWeights B U b S M hM label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA M residue z| ≤ ε)
    {V : Type*} [Fintype V] (point : V → EuclideanJetLayers U O)
    (spatial : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides → V → ℂ)
    (spatialProxy test : V → ℂ) (δ cap : V → ℝ)
    (hδ : ∀ t, 0 ≤ δ t) (htest : ∀ t, ‖test t‖ ≤ 1)
    (hspatial : ∀ w, (allocatedLongResidueWeights B U b S M hM label hsize).weight w ≠ 0 →
      ∀ t, ‖spatial w t - spatialProxy t‖ ≤ δ t)
    (hcap : ∀ w, (allocatedLongResidueWeights B U b S M hM label hsize).weight w ≠ 0 →
      ∀ t, g w (point t) ≤ cap t)
    {Z : ℝ} (hZ : 0 < Z) :
    let proxy := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA M residue (fun a => axis z.1 a.val) / scale))
    let error := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 * (ε / scale))
    ‖(allocatedLongResidueWeights B U b S M hM label hsize).complexMean
        (fun w => ∑ t, test t * (spatial w t * (g w (point t) : ℂ))) / (Z : ℂ) -
      (∑ t, test t * (spatialProxy t * (proxy (point t) : ℂ))) / (Z : ℂ)‖ ≤
      (∑ t, (δ t * cap t + ‖spatialProxy t‖ * error (point t))) / Z := by
  intro proxy error
  refine (allocatedLongResidueWeights B U b S M hM label hsize).norm_spatial_density_sum_error_normalized
    spatial spatialProxy (fun w t => g w (point t)) (fun t => proxy (point t))
    test δ cap (fun t => error (point t)) hδ htest hspatial ?_ ?_ hZ
  · intro w hw t
    rw [abs_of_nonneg (hg0 w (point t))]
    exact hcap w hw t
  · intro t
    exact allocatedPhysicalDensityFamily_residue_comparison B U b hR hσ S x u rows s hA
      hb o hσ1 C hC hchart hsmall bW d μ ν g hg hg0 hlaw
      M hM label hsize v₀ hv₀ hperiod residue hpoint (point t)

end Erdos3.VectorPolynomial

end

end OAI
