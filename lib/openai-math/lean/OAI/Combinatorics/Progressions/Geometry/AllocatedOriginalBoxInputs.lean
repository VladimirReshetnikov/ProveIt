import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (hx : ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
variable (X : Type*) [Fintype X] [DecidableEq X] (stride : X → ℕ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (hξ1 : ξ ≤ 1) (hτ1 : τ ≤ 1 / 2) (hsize : ∀ a, 4 ≤ τ * (N a : ℝ))
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (test : Finset (Fin dim) → (X → ℝ) → ℂ) (Z : ℝ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

omit [DecidableEq G] in
include hx hξ1 hτ1 hsize hbudget hbase in
theorem allocatedOriginalTupleSource_box_extension :
    allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))) Z poly hmem =
      allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem := by
  dsimp only [allocatedOriginalTupleSource]
  apply congrArg (fun z : ℂ => z / (Z : ℂ))
  apply (whole).complexMean_congr_support
  intro y hy
  apply tsum_congr
  intro z
  by_cases hz : z ∈ rectangularWeightIndices 0 widths 1
  · have heq := allocatedPhysicalCube_supported_testExtension B U b S (fun _ => 0) x y
      hx hy hbudget hτ hξ1 N hN hτ1 hsize test (⟨base, hbase⟩, ⟨z, hz⟩)
    rw [heq]
  · simp only [selectedResidueSmoothPMF_toReal,
      selectedResidueSmoothWeight_zero_off stride cells widths hwidths z hz,
      zero_div, Complex.ofReal_zero, zero_mul]

include hξ1 hτ1 hsize hbudget in
theorem allocatedOriginalTupleSource_box_extension_kernel_mean
    (kernelLaw : FiniteProbabilityWeights (G → IntegerScalarCubeBox (Fin dim) S.value))
    (hkernel : ∀ x, kernelLaw.weight x ≠ 0 →
      ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
    (bases : Finset (X → ℤ))
    (hbases : ∀ base ∈ bases, base ∈ trimmedIntegerBox N (spatialTrimMargin τ N)) :
    kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
      allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))) Z poly hmem) =
      kernelLaw.complexMean (fun x => 𝔼 base ∈ bases,
        allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass
          (physicalCubeSiteTest test) Z poly hmem) := by
  apply kernelLaw.complexMean_congr_support
  intro x hx
  apply Finset.expect_congr rfl
  intro base hbase
  exact allocatedOriginalTupleSource_box_extension B U b hR hσ S x (hkernel x hx) X stride hb o
    N hN hW hτ hξ hξ1 hτ1 hsize hbudget base (hbases base hbase) cells hmass test Z poly hmem

end Erdos3.VectorPolynomial

end

end OAI
