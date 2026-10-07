import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteAmbient

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

noncomputable def physicalEuclideanSitePoint (w : X → ℝ) (j : Fin m) : euclideanSubspace (U j) :=
  (euclideanSubspaceArrayEquiv (U j)).symm
    (fun _ : Unit => eval w (restrictCoefficients (U j) (p j) (hm j)))

omit [∀ j, Fintype (J j)] in
theorem physicalEuclideanSitePoint_apply (w : X → ℝ) (j : Fin m) (i : J j) :
    (physicalEuclideanSitePoint U p hm w j).val i = eval w (p j) i := by
  change (eval w (restrictCoefficients (U j) (p j) (hm j))).val i = _
  rw [eval_restrictCoefficients]

theorem physicalSingleSiteValue_eq_mk (d : ℕ) (w : X → ℝ) (j : Fin m) :
    physicalSingleSiteValue U d p hm w j () =
      QuotientAddGroup.mk ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j) := by
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  change euclideanSubspaceTorusEquiv (U j)
    ((euclideanSubspaceTorusEquiv (U j)).symm _) =
      euclideanSubspaceTorusEquiv (U j) (QuotientAddGroup.mk' _
        ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j))
  rw [AddEquiv.apply_symm_apply, euclideanSubspaceTorusEquiv_mk]
  congr 1

theorem physicalSingleSiteValue_projection (d : ℕ) [NeZero d] (w : X → ℝ) (j : Fin m) :
    quotientIntegerCover
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d
      (physicalSingleSiteValue U d p hm w j ()) =
        QuotientAddGroup.mk (physicalEuclideanSitePoint U p hm w j) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  change euclideanSubspaceTorusEquiv (U j)
    (d • (euclideanSubspaceTorusEquiv (U j)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
        (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))) = _
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  change quotientIntegerCover (subspaceArrayIntegerLattice Unit (U j)) d
      (QuotientAddGroup.mk' _ ((d : ℝ)⁻¹ •
        (fun _ : Unit => eval w (restrictCoefficients (U j) (p j) (hm j))))) =
      euclideanSubspaceTorusEquiv (U j) (QuotientAddGroup.mk' _ (physicalEuclideanSitePoint U p hm w j))
  rw [euclideanSubspaceTorusEquiv_mk, quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hd, one_smul]
  congr 1

end Erdos3.BooleanCubeKernel

end

end OAI
