import OAI.Combinatorics.Progressions.Geometry.AllocatedPhysicalChartBounds
import OAI.Combinatorics.Progressions.Geometry.PhysicalChartRadiusBudget
import OAI.Combinatorics.Progressions.Sampling.CoveredSamplerGlobalDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

def standardLatticeClosedQuarterBox (J : Type*) [Fintype J] : Set (EuclideanSpace ℝ J) :=
  {x | ∀ i, |x i| ≤ 1 / 4}

theorem standardLatticeClosedQuarterBox_isCompact (J : Type*) [Fintype J] :
    IsCompact (standardLatticeClosedQuarterBox J) := by
  have he : standardLatticeClosedQuarterBox J =
      (PiLp.homeomorph 2 (fun _ : J => ℝ)) ⁻¹'
        Set.Icc (fun _ => -(1 / 4 : ℝ)) (fun _ => (1 / 4 : ℝ)) := by
    ext x
    simp only [standardLatticeClosedQuarterBox, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_Icc, Pi.le_def, abs_le, forall_and]
    rfl
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : J => ℝ)).isClosedEmbedding.isCompact_preimage isCompact_Icc

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedCoveredDensity_global {α : Type*} [Fintype α] [DecidableEq α]
    {O E : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Fintype (E j)]
    (root : LayerSamplerVariables G I n B → ℤ)
    (A : Matrix α (LayerSamplerVariables G I n B) ℤ) (rows : ∀ j, O j → Finset α)
    (hroot : ∀ k, |(root k : ℝ) / layerSamplerBox B U b S k| ≤ 1)
    (hA : ∀ i k, |(A i k : ℝ) / layerSamplerBox B U b S k| ≤ 1)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
      id (pivot j)).det ≠ 0)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hjet : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) ≤ 1 / 4)
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (g : EuclideanJetLayers U O → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    (hlaw : (realDensityMeasure μ (fun y => allocatedCoefficientDensity B U b hb o hR hσ S
      (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d y))).map
      (euclideanCoefficientJetMap U root A rows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) g) :
    (∀ x, mixedCoveredJetCoordinates U o d x ∈
        coveredJetSourceRegion U b d (fun j _ => standardLatticeSmallBox (J j)) →
      g (coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d x)) =
        canonicalCoveredArrayDensity U root A rows pivot hpivot
          (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
          (allocatedLayerIntegerPMFs B U b hR hσ S) d x) ∧
    (∀ z ∉ coveredJetChart U b hb bW d ''
        coveredJetSourceRegion U b d (fun j _ => standardLatticeClosedQuarterBox (J j)), g z = 0) := by
  apply coefficientCoveredDensity_global U root A rows pivot hpivot
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S) o b hb bW d μ ν
    (fun j _ => standardLatticeClosedQuarterBox (J j)) (fun j _ => standardLatticeSmallBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_isCompact (J j))
    (fun j _ => standardLatticeSmallBox_isOpen (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    (fun _ _ => Set.Subset.rfl) (allocatedLayerWidths_pos B U b hR hσ S)
    (allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmall)
    (fun j a ha t i => allocatedLayerSupported_jet_quarter B U b hR hσ S root A rows
      hroot hA hσ1 o C hC hchart hjet j a ha t i) g hg hg0 hlaw

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))

local notation "root" => allocatedPhysicalCubeRoot B U b S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y

theorem allocatedPhysicalCoveredDensity_global
    {O E : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Fintype (E j)]
    (rows : ∀ j, O j → Finset α)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ j, ((boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).submatrix
      id (pivot j)).det ≠ 0)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    {H : ℝ} (hH : 1 ≤ H) (hc : allocatedPhysicalRootAllowance B U b S c ≤ H)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C H j)
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (g : EuclideanJetLayers U O → ℝ) (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    (hlaw : (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
      (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U root dirs rows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) g) :
    (∀ z, mixedCoveredJetCoordinates U o d z ∈
        coveredJetSourceRegion U b d (fun j _ => standardLatticeSmallBox (J j)) →
      g (coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d z)) =
        canonicalCoveredArrayDensity U root dirs rows pivot hpivot
          (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
          (allocatedLayerIntegerPMFs B U b hR hσ S) d z) ∧
    (∀ z ∉ coveredJetChart U b hb bW d ''
        coveredJetSourceRegion U b d (fun j _ => standardLatticeClosedQuarterBox (J j)), g z = 0) := by
  have hHc := allocatedPhysicalRootAllowance_one_le B U b S c
  have hjet := allocatedPhysicalChartRadius_bound (G := G) B α C hC hH
    (fun j => (hR j).le) hsmall hHc hc
  have hsmallChart := allocatedJetRadius_implies_chartRadius (B := B) (hR := hR) hHc C hC hjet
  apply coefficientCoveredDensity_global U root dirs rows pivot hpivot
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S) o b hb bW d μ ν
    (fun j _ => standardLatticeClosedQuarterBox (J j)) (fun j _ => standardLatticeSmallBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_isCompact (J j))
    (fun j _ => standardLatticeSmallBox_isOpen (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    (fun _ _ => Set.Subset.rfl) (allocatedLayerWidths_pos B U b hR hσ S)
    (allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmallChart)
    (fun j a ha t i => allocatedLayerSupported_jet_root_allowance B U b hR hσ S root dirs rows
      hHc (allocatedPhysicalCube_root_normalized B U b S x y c)
      (allocatedPhysicalCube_directions_normalized B U b S x y)
      hσ1 o C hC hchart hjet j a ha t i) g hg hg0 hlaw

end Erdos3.VectorPolynomial

end

end OAI
