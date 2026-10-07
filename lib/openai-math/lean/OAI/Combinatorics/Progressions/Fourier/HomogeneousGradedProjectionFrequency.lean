import OAI.Combinatorics.Progressions.Estimates.GradedPieceRepresentative
import OAI.Combinatorics.Progressions.Linear.HomogeneousGradedProjectionBounds

namespace OAI

section

namespace Erdos3

open Module

variable {K V W ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

theorem graded_image_frequency_zero
    (b : Basis ι K V) (ω : ι → ℕ) (c : Basis κ K W) (ν : κ → ℕ)
    (T : V →ₗ[K] W) (s : ℕ)
    (hT : ∀ x, T (basisGradeProjection b ω s x) = basisGradeProjection c ν s (T x))
    (U : Submodule K V) (hU : BasisGradedSubmodule b ω U) (η : W →ₗ[K] K)
    (hsource : ∀ x ∈ U, basisGradeProjection b ω s x = x → η (T x) = 0)
    {y : W} (hy : y ∈ U.map T) (hgrade : basisGradeProjection c ν s y = y) :
    η y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h := hsource (basisGradeProjection b ω s x) (hU s x hx)
    (basisCoordinateProjection_idempotent b {i | ω i = s} x)
  rwa [hT, hgrade] at h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedFrequency (η : L →ₗ[ℚ] ℚ) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  η.comp (b.repr.symm.toLinearMap.comp (F.associatedGradedBasis b ω hF).repr.toLinearMap)

theorem gradedFrequency_projection (η : L →ₗ[ℚ] ℚ) (j : ℕ) (x : L) :
    F.gradedFrequency b ω hF η (F.gradedPieceProjection b ω hF j x) =
      η (basisGradeProjection b ω j x) := by
  change η (b.repr.symm ((F.associatedGradedBasis b ω hF).repr
    ((F.associatedGradedBasis b ω hF).repr.symm (b.repr (basisGradeProjection b ω j x))))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

include hF in
theorem basisGradeProjection_top (x : F.layer s) : basisGradeProjection b ω s (x : L) = x := by
  have he : {i | ω i = s} = {i | s ≤ ω i} := by
    ext i
    exact ⟨fun h => h.ge, fun h => le_antisymm (F.adaptedBasis_weight_le_step b ω hF i) h⟩
  change basisCoordinateProjection b {i | ω i = s} (x : L) = x
  rw [he]
  exact basisCoordinateProjection_eq_self b _ _ ((hF s) ▸ x.property)

theorem gradedFrequency_top_piece (η : L →ₗ[ℚ] ℚ) (x : F.layer s) :
    F.gradedFrequency b ω hF η (F.associatedGradedPieceMap s x) = η x := by
  rw [← F.gradedPieceProjection_eq_pieceMap b ω hF, F.gradedFrequency_projection,
    F.basisGradeProjection_top b ω hF x]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem gradedFrequency_top_natural (η : M →ₗ[ℚ] ℚ) (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis e ω hF) ω s x = x) :
    F.gradedFrequency e ω hF (η.comp φ.toLinearMap) x =
      G.gradedFrequency f ν hG η (F.associatedGradedMap G φ hφ x) := by
  obtain ⟨v, rfl⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF s x hx
  rw [F.associatedGradedMap_piece, F.gradedFrequency_top_piece,
    G.gradedFrequency_top_piece]
  rfl

theorem gradedFrequency_comap_top_zero (η : M →ₗ[ℚ] ℚ)
    (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hzero : ∀ y ∈ U, basisGradeProjection (G.associatedGradedBasis f ν hG) ν s y = y →
      G.gradedFrequency f ν hG η y = 0) :
    ∀ x ∈ U.comap (F.associatedGradedMap G φ hφ),
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s x = x →
        F.gradedFrequency e ω hF (η.comp φ.toLinearMap) x = 0 := by
  intro x hx hpure
  rw [F.gradedFrequency_top_natural G e ω hF f ν hG φ hφ η x hpure]
  apply hzero _ hx
  exact (F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ s x).symm.trans
    (congrArg (F.associatedGradedMap G φ hφ) hpure)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}

theorem homogeneousAssociatedGradedEquiv_pieceMap
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (j : ℕ) (x : F.layer j) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedPieceMap j x) =
      basisGradeProjection b ω j x.val :=
  F.associatedGradedPieceMap_repr_symm b ω hF j x

theorem homogeneousAssociatedGradedEquiv_top_piece
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (x : F.layer s) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedPieceMap s x) = x.val := by
  rw [F.homogeneousAssociatedGradedEquiv_pieceMap b ω hF hb,
    F.basisGradeProjection_top b ω hF x]

variable (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_top_frequency (η : M →ₗ[ℚ] ℚ)
    (x : F.AssociatedGraded)
    (hx : basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x) :
    η (F.homogeneousGradedProjection G c ν hG hc φ hφ x) =
      F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x := by
  obtain ⟨v, hv⟩ := F.exists_associatedGradedPieceMap_of_pure b ω hF s x hx
  rw [← hv, F.gradedFrequency_top_piece]
  change η (G.homogeneousAssociatedGradedEquiv c ν hG hc
    (F.associatedGradedMap G φ hφ (F.associatedGradedPieceMap s v))) = η (φ v.val)
  rw [F.associatedGradedMap_piece G φ hφ,
    G.homogeneousAssociatedGradedEquiv_top_piece c ν hG hc]

theorem homogeneousGradedProjection_top_frequency_zero
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (η : M →ₗ[ℚ] ℚ)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x = 0)
    {y : M} (hy : y ∈ W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ))
    (htop : y ∈ G.layer s) : η y = 0 := by
  apply graded_image_frequency_zero (F.associatedGradedBasis b ω hF) ω c ν
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap s
    (F.homogeneousGradedProjection_gradeProjection G c ν hG hc φ hφ b ω hF s)
    W.toSubmodule hW η ?_ hy (G.basisGradeProjection_top c ν hG ⟨y, htop⟩)
  intro x hx hpure
  exact (F.homogeneousGradedProjection_top_frequency G c ν hG hc φ hφ b ω hF η x hpure).trans
    (hη x hx hpure)

theorem homogeneousGradedProjection_top_le_frequency_ker
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (η : M →ₗ[ℚ] ℚ)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF (η.comp φ.toLinearMap) x = 0) :
    (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)).toSubmodule ⊓ G.layer s ≤
      LinearMap.ker η := by
  intro y hy
  exact F.homogeneousGradedProjection_top_frequency_zero G c ν hG hc φ hφ b ω hF W hW η hη
    hy.1 hy.2

end Erdos3.NilpotentLieFiltration

end

end OAI
