import OAI.Combinatorics.Progressions.Estimates.UniformFrozenDescent

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ : Type*}

def reindexWeightSurvivors (s : ℕ) (ω : ι → ℕ) (e : ι ≃ κ) :
    QuotientTopBasisIndex s ω ≃ QuotientTopBasisIndex s (fun k => ω (e.symm k)) where
  toFun i := ⟨e i.val, by simpa only [Equiv.symm_apply_apply] using i.property⟩
  invFun i := ⟨e.symm i.val, i.property⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv i := by apply Subtype.ext; exact e.apply_symm_apply i.val

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem quotientTopBasis_reindex (e : ι ≃ κ)
    (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)})) :
    F.quotientTopBasis (b.reindex e) (fun k => ω (e.symm k)) hF' =
      (F.quotientTopBasis b ω hF).reindex (reindexWeightSurvivors s ω e) := by
  apply DFunLike.ext
  intro i
  simp only [F.quotientTopBasis_apply, Basis.reindex_apply]
  rfl

variable [Fintype ι]

noncomputable def reducedSquareFinIndexEquiv (s : ℕ) (ω : ι → ℕ) :
    ReducedSquareBasisIndex s ω ≃
      Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) :=
  (reindexWeightSurvivors s (squareBasisWeight ω) (Fintype.equivFin _)).trans (Fintype.equivFin _)

theorem reducedSquareFinIndexEquiv_weight
    (i : Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i})) :
    quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i} i =
      squareBasisWeight ω ((reducedSquareFinIndexEquiv s ω).symm i).val := rfl

theorem squareTopQuotientModel_basis_reindex (Γ : Subgroup F.squareFiltration.Group)
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
    (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N) :
    (F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
      (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).basis =
        (F.reducedSquareBasis b ω hF).reindex (reducedSquareFinIndexEquiv s ω) := by
  change (F.squareFiltration.quotientTopBasis (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
    (F.squareFinBasis_layers b ω hF)).reindex (Fintype.equivFin _) = _
  have hb := F.squareFiltration.quotientTopBasis_reindex
    (F.adaptedSquareBasis b ω (hF 2)) (squareBasisWeight ω) (F.adaptedSquareBasis_layers b ω hF)
    (Fintype.equivFin _) (F.squareFinBasis_layers b ω hF)
  calc
    _ = ((F.reducedSquareBasis b ω hF).reindex
        (reindexWeightSurvivors s (squareBasisWeight ω) (Fintype.equivFin _))).reindex
          (Fintype.equivFin _) := congrArg (fun c => c.reindex (Fintype.equivFin _)) hb
    _ = _ := by
      apply DFunLike.ext
      intro i
      simp only [Basis.reindex_apply]
      exact (Basis.reindex_apply (F.reducedSquareBasis b ω hF)
        (reducedSquareFinIndexEquiv s ω) i).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
