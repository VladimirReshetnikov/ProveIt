import OAI.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency

namespace OAI

section

namespace Erdos3

open Module

theorem basisGradeProjection_reindex {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (ω : ι → ℕ) (e : ι ≃ κ) (j : ℕ) :
    basisGradeProjection (b.reindex e) (fun k => ω (e.symm k)) j = basisGradeProjection b ω j := by
  apply LinearMap.ext
  intro x
  apply (b.reindex e).repr.injective
  ext k
  simp only [basisGradeProjection_repr, Basis.repr_reindex_apply]

theorem basisGradedSubmodule_reindex_iff {K V ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V] (b : Basis ι K V) (ω : ι → ℕ) (e : ι ≃ κ)
    (U : Submodule K V) :
    BasisGradedSubmodule (b.reindex e) (fun k => ω (e.symm k)) U ↔ BasisGradedSubmodule b ω U := by
  simp only [BasisGradedSubmodule, basisGradeProjection_reindex]

namespace NilpotentLieFiltration

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))

theorem associatedGradedBasis_reindex :
    F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF' =
      (F.associatedGradedBasis b ω hF).reindex e := by
  apply DFunLike.ext
  intro k
  rw [Basis.reindex_apply]
  rw [← F.associatedGradedPieceMap_basis (b.reindex e) (fun k => ω (e.symm k)) hF'
      (ω (e.symm k)) k le_rfl rfl,
    ← F.associatedGradedPieceMap_basis b ω hF (ω (e.symm k)) (e.symm k) le_rfl rfl]
  congr 1
  apply Subtype.ext
  exact Basis.reindex_apply b e k

theorem gradedFrequency_reindex (η : L →ₗ[ℚ] ℚ) :
    F.gradedFrequency (b.reindex e) (fun k => ω (e.symm k)) hF' η =
      F.gradedFrequency b ω hF η := by
  apply LinearMap.ext
  intro x
  change η ((b.reindex e).repr.symm
      ((F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF').repr x)) =
    η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr x))
  rw [F.associatedGradedBasis_reindex b ω hF e hF']
  apply congrArg η
  apply (b.reindex e).repr.injective
  ext k
  simp only [LinearEquiv.apply_symm_apply, Basis.repr_reindex_apply]

end NilpotentLieFiltration
end Erdos3

end

end OAI
