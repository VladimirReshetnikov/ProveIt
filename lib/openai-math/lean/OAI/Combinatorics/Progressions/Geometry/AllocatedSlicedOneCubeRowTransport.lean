import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedProductPrefactorCap
import OAI.Combinatorics.Progressions.Estimates.AllocatedWholeProfileRowReindex

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "rows" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "e" => (fun j => Equiv.symm (oneCubeRowsEquiv (rowSets j) (hrows j)))
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [∀ a, DecidableEq (B a)] in
theorem allocatedWholeMaskedSlicedProfile_oneCube_rows
    (w : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
    (q : ℕ) (y : EuclideanJetLayers U (fun _ => Finset (Fin 1))) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x (fun j => (Subtype.val : rows j → Finset (Fin 1)))
      hb o bW d w q (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width)
        (euclideanJetRowsReindex e U y) =
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x (fun _ => id) hb o bW d w q
        (allocatedSlicedPhysicalJetIdeal B U b S hR hB lower width) y :=
  allocatedWholeMaskedCoveredProfile_reindex_rows B U b hR hσ S x e (fun _ => id) hb o bW d w q _ y

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, SigmaFinite (ν j)]

omit [∀ a, DecidableEq (B a)] in
theorem allocatedWholeMaskedSlicedProfile_oneCube_mean_integral
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (w : A → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin 1) (allocatedPrincipalSides B U b S))
    (q : ℕ) (F : EuclideanJetLayers U rows → ℂ) :
    (∫ y, (p.mean (fun a => allocatedWholeMaskedCoveredProfile B U b hR hσ S x
      (fun j => (Subtype.val : rows j → Finset (Fin 1))) hb o bW d (w a) q
      (allocatedSlicedRowIdeal B U b S rowSets hR hrows hB lower width) y) : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : rows j => ν j))) =
      ∫ y, (p.mean (fun a => allocatedWholeMaskedCoveredProfile B U b hR hσ S x (fun _ => id)
        hb o bW d (w a) q (allocatedSlicedPhysicalJetIdeal B U b S hR hB lower width) y) : ℂ) *
          F (euclideanJetRowsReindex e U y)
            ∂Measure.pi (fun j => Measure.pi (fun _ : Finset (Fin 1) => ν j)) :=
  allocatedWholeMaskedCoveredProfile_reindex_mean_integral B U b hR hσ S x e (fun _ => id)
    hb o bW d ν p w q _ F

end Erdos3.VectorPolynomial

end

end OAI
