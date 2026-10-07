import OAI.Combinatorics.Progressions.Geometry.AllocatedJetSupportBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedIntegerKernelPMF_zero_off_box (j : Fin m) (i : Fin (n j))
    (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)
    {P : ℝ} (hP : 0 ≤ P) (hRP : R j ≤ Real.exp P) (z : O j → ℤ)
    (hz : z ∉ rectangularWeightIndices (fun _ => 0) (fun _ => (basisAxisScale (basis j) i : ℝ))
      (Real.exp (allocatedJetSupportLog (G := G) B α O P))) :
    allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous z = 0 := by
  exact coefficientImagePMF_zero_off_box (allocatedPartitionedJetMatrix B U basis S x u v rows j)
    (allocatedIntegerProfileScales B U basis S j i) (fun _ => (basisAxisScale (basis j) i : ℝ))
    (allocatedIntegerProfileScales_pos B U basis S j i)
    (fun _ => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    (affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i))
    (affineProductProfile_nonneg _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i))
    (allocatedIntegerProfile_support B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)
    (allocatedPartitionedJet_radius_bound B U basis S x u v rows j i hP (hR j).le hRP) z hz

end Erdos3.VectorPolynomial

end

end OAI
