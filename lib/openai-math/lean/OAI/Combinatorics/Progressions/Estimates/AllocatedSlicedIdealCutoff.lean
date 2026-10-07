import OAI.Combinatorics.Progressions.Geometry.AllocatedSlicedRowIdealSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
variable (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card (Fin 1) * ((Fintype.card (Fin 1) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable [∀ a, DecidableEq (B a)]

include hT hsource hradius hC hchart hbudget in

theorem allocatedSlicedRowIdeal_cutoff_fixes
    (hσ1 : ∀ j, σ j ≤ 1) (h4 : ∀ j, 4 ≤ T j)
    (hrows : ∀ j t, t ∈ rowSets j)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (x : G → IntegerScalarCubeBox (Fin 1) S.value)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
    (q : ℕ) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y *
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q
        (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y : ℂ) =
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q
        (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y : ℂ) := by
  apply allocatedProductSiteCutoff_fixes_source B U b S rowSets o hb bW d r hr hR hσ T hT hsource hradius C hC hchart hbudget hσ1 x y₀ q
  intro v hv a₀ t
  exact (allocatedSlicedRowIdeal_coordinate_support B U b S rowSets hR hrows hB lower width
    hwidth ha hδ hprincipal hw hl v hv a₀ t).trans (mul_le_mul_of_nonneg_right (h4 _) (hR _).le)

include hT hsource hradius hC hchart hbudget in

theorem allocatedSlicedRowIdeal_cutoff_fixes_mean
    (hσ1 : ∀ j, σ j ≤ 1) (h4 : ∀ j, 4 ≤ T j)
    (hrows : ∀ j t, t ∈ rowSets j)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (x : G → IntegerScalarCubeBox (Fin 1) S.value)
    {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω)
    (tuples : Ω → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
    (q : ℕ) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y *
      ((weights).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (tuples u) q
        (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y) : ℂ) =
      ((weights).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (tuples u) q
        (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y) : ℂ) := by
  simp only [← weights.complexMean_ofReal]
  rw [← weights.complexMean_mul_left]
  apply congrArg weights.complexMean
  funext u
  exact allocatedSlicedRowIdeal_cutoff_fixes B U b S rowSets o hb bW d r hr hR hσ T hT hsource hradius C hC hchart hbudget
    hσ1 h4 hrows hB lower width hwidth ha hδ hprincipal hw hl x (tuples u) q y

end Erdos3.VectorPolynomial

end

end OAI
