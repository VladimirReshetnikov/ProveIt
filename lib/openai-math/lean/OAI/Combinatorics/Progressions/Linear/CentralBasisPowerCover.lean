import OAI.Combinatorics.Progressions.Lattices.LatticeOrderedGenerators

namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem subgroupPowerCover_index_le (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ d := by
  obtain ⟨a, ha⟩ := he.exists_surjective_orderedZpowProduct hnil Γ l hl hgrid
  have h := powerSubgroup_index_le_of_ordered_generators a ha m hm
  simpa only [Subgroup.relIndex, subgroupPowerCover_subgroupOf] using h

theorem powerCover_of_central_basis
    (Λ₀ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m₀ m : ℕ)
    (hl : 0 < l) (hm : 0 < m)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    (hdiv : l * m₀ ∣ m) :
    subgroupPowerCover Γ m ≤ Λ₀ ∧ subgroupPowerCover Γ m ≤ Γ ∧
      ((subgroupPowerCover Γ m).subgroupOf Γ).Characteristic ∧
      ((subgroupPowerCover Γ m).subgroupOf Γ).Normal ∧
      ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ d ∧
      scaledIntegerGrid (m * l) ⊆ bchSubgroupCoordinates e (subgroupPowerCover Γ m) ∧
      bchSubgroupCoordinates e (subgroupPowerCover Γ m) ⊆ denominatorGrid (m * l) := by
  obtain ⟨hfinite, hindex⟩ := he.subgroupPowerCover_index_le hnil Γ l hl houter m hm
  exact ⟨subgroupPowerCover_le_of_grid e Γ Λ₀ l m₀ m houter htarget hdiv,
    subgroupPowerCover_le Γ m, inferInstance, inferInstance, hfinite, hindex,
    subgroupPowerCover_grid e Γ l m hinner houter⟩

end Erdos3.IsCentralLieBasis

end

end OAI
