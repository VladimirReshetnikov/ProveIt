import OAI.Combinatorics.Progressions.Linear.CentralBasisPowerCover

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem subgroupPowerCover_index_le (e : Basis ι ℚ L) (Γ : Subgroup F.Group)
    (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ Fintype.card ι := by
  let : FiniteDimensional ℚ L := Module.Finite.of_basis e
  obtain ⟨b, hb⟩ := F.exists_central_basis
  obtain ⟨N, hN, hgrid⟩ := exists_bchSubgroup_outer_grid_change_basis e b Γ l hl houter
  simpa only [finrank_eq_card_basis e] using
    hb.subgroupPowerCover_index_le F.lowerCentralSeries_eq_bot Γ N hN hgrid m hm

theorem exists_ordered_integral_generators (e : Basis ι ℚ L) (Γ : Subgroup F.Group)
    (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ a : Fin (Fintype.card ι) → Γ, Function.Surjective (orderedZpowProduct a) := by
  let : FiniteDimensional ℚ L := Module.Finite.of_basis e
  obtain ⟨b, hb⟩ := F.exists_central_basis
  obtain ⟨N, hN, hgrid⟩ := exists_bchSubgroup_outer_grid_change_basis e b Γ l hl houter
  rw [← finrank_eq_card_basis e]
  exact hb.exists_surjective_orderedZpowProduct F.lowerCentralSeries_eq_bot Γ N hN hgrid

end Erdos3.NilpotentLieFiltration

end

end OAI
