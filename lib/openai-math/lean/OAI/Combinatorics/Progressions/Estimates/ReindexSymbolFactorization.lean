import OAI.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
import OAI.Combinatorics.Progressions.Linear.ReindexGradedBasis

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))

theorem symbolFactorizationIn_reindex_iff (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.SymbolFactorizationIn (b.reindex e) (fun k => ω (e.symm k)) hF' T X p l W ↔
      F.SymbolFactorizationIn b ω hF T X p l W := by
  simp only [SymbolFactorizationIn,
    F.symbolSlowBound_reindex_iff b ω hF e hF',
    F.symbolRationalGrid_reindex_iff b ω hF e hF',
    F.symbolPointwiseSubalgebra_basis_independent b ω hF
      (b.reindex e) (fun k => ω (e.symm k)) hF']

theorem graded_top_annihilation_reindex_iff (η : L →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection
        (F.associatedGradedBasis (b.reindex e) (fun k => ω (e.symm k)) hF')
        (fun k => ω (e.symm k)) s x = x →
      F.gradedFrequency (b.reindex e) (fun k => ω (e.symm k)) hF' η x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) := by
  rw [F.associatedGradedBasis_reindex b ω hF e hF',
    F.gradedFrequency_reindex b ω hF e hF' η]
  simp only [basisGradeProjection_reindex]

theorem symbolFactorizationIn_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (T : σ → ℝ) (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (p : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.SymbolFactorizationIn c ν hC T X p l W ↔ F.SymbolFactorizationIn b ω hF T X p l W := by
  subst c
  subst ν
  exact F.symbolFactorizationIn_reindex_iff b ω hF e hC T X p l W

theorem graded_top_annihilation_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (η : L →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis c ν hC) ν s x = x →
      F.gradedFrequency c ν hC η x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) := by
  subst c
  subst ν
  exact F.graded_top_annihilation_reindex_iff b ω hF e hC η W

theorem graded_submodule_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis c ν hC) ν U ↔
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U := by
  subst c
  subst ν
  rw [F.associatedGradedBasis_reindex b ω hF e hC]
  exact basisGradedSubmodule_reindex_iff (F.associatedGradedBasis b ω hF) ω e U

theorem associatedGradedBasis_repr_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (x : F.AssociatedGraded) (i : ι) :
    (F.associatedGradedBasis c ν hC).repr x (e i) =
      (F.associatedGradedBasis b ω hF).repr x i := by
  subst c
  subst ν
  rw [F.associatedGradedBasis_reindex b ω hF e hC,
    Basis.repr_reindex_apply, Equiv.symm_apply_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
