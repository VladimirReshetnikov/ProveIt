import OAI.Combinatorics.Progressions.Nilpotent.AdaptedBasisNilmanifold
import OAI.Combinatorics.Progressions.Sampling.SupportedQuotientExactGrid

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

noncomputable def quotientFinBasis :
    Basis (Fin (Fintype.card {i // i ∉ S})) ℚ (L ⧸ I) :=
  (supportedQuotientBasis b I.toSubmodule S hspan).reindex (Fintype.equivFin _)

noncomputable def quotientFinWeight : Fin (Fintype.card {i // i ∉ S}) → ℕ :=
  fun i => w ((Fintype.equivFin {i // i ∉ S}).symm i)

include hlayers in
theorem quotientFinBasis_layers (j : ℕ) :
    (F.quotientLie I hI).layer j = Submodule.span ℚ
      (quotientFinBasis b I S hspan '' {i | j ≤ quotientFinWeight w S i}) := by
  rw [F.supportedQuotientBasis_layers b w hlayers I hI S hspan]
  exact (basis_reindex_span_weights (L := L ⧸ I)
    (supportedQuotientBasis b I.toSubmodule S hspan) (Fintype.equivFin _)
    (fun i => w i) j).symm

noncomputable def coordinateQuotientModel (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold (L ⧸ I) t (Fintype.card {i // i ∉ S}) :=
  (F.quotientLie I hI).ofAdaptedBasis (quotientFinBasis b I S hspan)
    (quotientFinWeight w S) (F.quotientFinBasis_layers b w hlayers I hI S hspan)
    (Γ.map (F.quotientStepHom I hI)) N hN
    (bchSubgroup_inner_grid_reindex _ (Fintype.equivFin _) _
      (F.quotientStep_inner_grid_supported b I hI S hspan Γ hin))
    (bchSubgroup_outer_grid_reindex _ (Fintype.equivFin _) _
      (F.quotientStep_outer_grid_supported b I hI S hspan Γ hout))

theorem coordinateQuotientModel_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hNp : (N : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ p) :
    (F.coordinateQuotientModel b w hlayers I hI S hspan Γ N hN hin hout).GeometryComplexityLE p := by
  apply (F.quotientLie I hI).ofAdaptedBasis_geometry _ _ _ _ _ _ _ _ hp
  · exact (Nat.cast_le.mpr (Fintype.card_subtype_le (fun i => i ∉ S))).trans hd
  · exact hNp
  · intro i j k
    simp only [quotientFinBasis, lieStructureConstants_reindex, supportedQuotientBasis_lieStructure]
    exact hc _ _ _

end Erdos3.NilpotentLieFiltration

end

end OAI
