import OAI.Combinatorics.Progressions.Fourier.StandardJetFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

theorem coveredJetAmbientTorus_booleanSite (d : ℕ) (y : EuclideanJetLayers U jets)
    (s : Finset α) (j : Fin m) (i : J j) :
    coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s) ⟨j, (), i⟩ =
      ∑ r : jets j, boundedBooleanReconstructionMatrix α (j.val + 1) s r •
        coveredJetAmbientTorus U d y ⟨j, r, i⟩ := by
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (quotientIntegerCover (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j))).toAddSubgroup d
      (∑ r : jets j, boundedBooleanReconstructionMatrix α (j.val + 1) s r • y j r))) i = _
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  rfl

theorem coveredJetAmbientTorus_booleanInverse (d : ℕ) (y : EuclideanJetLayers U jets)
    (j : Fin m) (r : jets j) (i : J j) :
    (∑ s : Finset α, booleanJetExtractionMatrix Subtype.val r s •
      coveredJetAmbientTorus U d (coveredBooleanSiteValue U y s) ⟨j, (), i⟩) =
      coveredJetAmbientTorus U d y ⟨j, r, i⟩ := by
  simp_rw [coveredJetAmbientTorus_booleanSite]
  exact boundedBooleanReconstruction_zsmul_inverse (j.val + 1)
    (fun t => coveredJetAmbientTorus U d y ⟨j, t, i⟩) r

end Erdos3.VectorPolynomial

end

end OAI
