import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedDataComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem ambientGridError_eq_forecastJointGridError (ξ : ℝ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Lip : ℝ≥0} {δ δgrid : ℝ} (hδ : 0 < δ) (cutoff : ℕ) :
    allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := b) (S := S) (E := Eout)
      (τ := τ) (ξ := ξ) (box := physicalN) (integerFrame := slice.path.noise)
      (HG := slice.kernelLength) (hHG := slice.kernelLength_two) (cG := slice.kernelStart)
      (stepG := slice.step) (hstepG := slice.step_pos) (e := spatialEquiv)
      (h0 := slice.analyticKernelDetFalse ξ) (h1 := slice.analyticKernelDetTrue ξ)
      (hδ := hδ) (o := o) (Lip := Lip) (cutoff := cutoff) (D := slice.decayConstant) (δgrid := δgrid) =
    forecastJointGridError
      (Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))))
      (Fintype.card (X ⊕ AllocatedActiveIntegerAxis U b S.value))
      (Fintype.card (Σ j, I j)) cutoff slice.decayConstant
      (fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
        (slice.slicedBlockEquiv true) (div_pos hδ (by norm_num : (0 : ℝ) < 2)))
      (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) (div_pos hδ (by norm_num : (0 : ℝ) < 2)))
      (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R)) δgrid := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  unfold allocatedSlicedPhysicalAmbientGridError
  dsimp only
  unfold slicedBlockEquiv
  congr 4

end ActualFixedSpatialSlicedForecastPath

namespace ActualFixedSpatialForecastSetup

variable {B U b S Dmod τ δslice}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)

include s in
omit decX in
theorem gridDimensions_le :
    Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))) ≤
        Dmod + Fintype.card (Σ j, I j) ∧
      Fintype.card (X ⊕ AllocatedActiveIntegerAxis U b S.value) ≤
        Dmod + Fintype.card (Σ j, I j) ∧
      Fintype.card (Σ j, I j) ≤ Dmod + Fintype.card (Σ j, I j) := by
  have hout : Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) ≤ Dmod := by
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hi : Fintype.card (AllocatedActiveIntegerAxis U b S.value) ≤ ∑ j, n j := by
    calc
      _ ≤ Fintype.card (Σ j : Fin m, Fin (n j)) :=
        Fintype.card_le_of_injective (fun a : AllocatedActiveIntegerAxis U b S.value => a.val)
          (fun _ _ h => Subtype.ext h)
      _ = _ := by simp
  have hjoint : Fintype.card (X ⊕ AllocatedActiveIntegerAxis U b S.value) ≤ Dmod := by
    rw [Fintype.card_sum]
    calc
      _ ≤ Fintype.card X + ∑ j : Fin m, n j := Nat.add_le_add_left hi _
      _ ≤ Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun j _ => Nat.le_add_left _ _)) _
      _ ≤ _ := s.hDmod
  exact ⟨hout.trans (Nat.le_add_right _ _), hjoint.trans (Nat.le_add_right _ _), Nat.le_add_left _ _⟩

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

end OAI
