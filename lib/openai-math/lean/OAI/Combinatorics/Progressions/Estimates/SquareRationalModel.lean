import OAI.Combinatorics.Progressions.Linear.SquareBasisGeometry
import OAI.Combinatorics.Progressions.Nilpotent.AdaptedBasisNilmanifold

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareFinBasis (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) :
    Basis (Fin (Fintype.card (ι ⊕ {i // 2 ≤ w i}))) ℚ F.squareLieSubalgebra :=
  (F.adaptedSquareBasis b w h).reindex (Fintype.equivFin _)

noncomputable def squareFinWeight (w : ι → ℕ) :
    Fin (Fintype.card (ι ⊕ {i // 2 ≤ w i})) → ℕ :=
  fun i => squareBasisWeight w ((Fintype.equivFin _).symm i)

theorem squareFinBasis_layers (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (j : ℕ) :
    F.squareFiltration.layer j = Submodule.span ℚ
      (F.squareFinBasis b w (hlayers 2) '' {i | j ≤ squareFinWeight w i}) := by
  rw [F.adaptedSquareBasis_layers b w hlayers j]
  exact (basis_reindex_span_weights _ _ _ _).symm

theorem exists_square_rational_model (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (Γ : Subgroup F.Group) {l H : ℕ} (hl : 0 < l) (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (N : ℕ) (hN : 0 < N)
      (hinner : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (F.squareFinBasis b w (hlayers 2)) (F.squareLattice Γ))
      (houter : bchSubgroupCoordinates (F.squareFinBasis b w (hlayers 2))
        (F.squareLattice Γ) ⊆ denominatorGrid N),
      (F.squareFiltration.ofAdaptedBasis (F.squareFinBasis b w (hlayers 2))
        (squareFinWeight w) (F.squareFinBasis_layers b w hlayers)
        (F.squareLattice Γ) N hN hinner houter).GeometryComplexityLE ((p + 2) ^ 11) := by
  obtain ⟨N, hN, hNp, hinner, houter⟩ :=
    F.exists_adaptedSquareBasis_grid b w (hlayers 2) Γ hl hin hout hp hd hlp
  have hin' := bchSubgroup_inner_grid_reindex _ (Fintype.equivFin _) _ hinner
  have hout' := bchSubgroup_outer_grid_reindex _ (Fintype.equivFin _) _ houter
  refine ⟨N, hN, hin', hout', ?_⟩
  apply F.squareFiltration.ofAdaptedBasis_geometry _ _ _ _ _ _ hin' hout' (by positivity)
  · exact ((Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)).trans
        (le_power_budget hp (by decide : 1 ≤ 11))
  · exact hNp.trans (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 9 ≤ 11)))
  · intro i j k
    change rationalLogHeight
      (lieStructureConstants (F.squareFinBasis b w (hlayers 2)) i j k) ≤ (p + 2) ^ 11
    rw [squareFinBasis, lieStructureConstants_reindex]
    exact F.adaptedSquareBasis_structure_bound b w (hlayers 2) hH hc hp hd hHp _ _ _

end Erdos3.NilpotentLieFiltration

end

end OAI
