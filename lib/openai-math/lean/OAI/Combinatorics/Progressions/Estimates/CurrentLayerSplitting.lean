import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem bch_triple_sub_sum_mem_next_layer (k : ℕ) (a p d : L)
    (ha : a ∈ F.layer k) (hd : d ∈ F.layer k) :
    lieBCH s (lieBCH s a p) d - (a + p + d) ∈ F.layer (k + 1) := by
  have hp : p ∈ F.layer 1 := by simp only [F.one_eq_top, Submodule.mem_top]
  have hap : lieBCH s a p ∈ F.layer 1 := by
    simp only [F.one_eq_top, Submodule.mem_top]
  have h₁ := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot
    (F.layerIdeal (k + 1)) a p (F.lie_mem ha hp)
  have h₂ := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot
    (F.layerIdeal (k + 1)) (lieBCH s a p) d
    (by
      change ⁅lieBCH s a p, d⁆ ∈ F.layer (k + 1)
      simpa only [Nat.add_comm 1 k] using F.lie_mem hap hd)
  have h := (F.layer (k + 1)).add_mem h₂ h₁
  convert h using 1
  abel

theorem inv_mul_coord_mem_layer_of_quotient_eq (k : ℕ) (a b : F.Group)
    (h : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) a =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) b) :
    (a⁻¹ * b).coord ∈ F.layer k := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal k) _).mp
  have hq : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact congrArg NilpotentLieBCHGroup.coord hq

theorem mul_inv_coord_mem_layer_of_quotient_eq (k : ℕ) (a b : F.Group)
    (h : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) a =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) b) :
    (a * b⁻¹).coord ∈ F.layer k := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal k) _).mp
  have hq : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact congrArg NilpotentLieBCHGroup.coord hq

theorem normalized_splitting_sub_sum_mem_next_layer (k : ℕ)
    (E P R E₀ R₀ : F.Group)
    (hE : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) E₀ =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) E)
    (hR : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) R =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) R₀) :
    (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord -
      ((E₀⁻¹ * E).coord + P.coord + (R * R₀⁻¹).coord) ∈ F.layer (k + 1) := by
  have heq : E₀⁻¹ * (E * P * R) * R₀⁻¹ = (E₀⁻¹ * E) * P * (R * R₀⁻¹) := by
    simp only [mul_assoc]
  rw [heq]
  exact F.bch_triple_sub_sum_mem_next_layer k _ _ _
    (F.inv_mul_coord_mem_layer_of_quotient_eq k E₀ E hE)
    (F.mul_inv_coord_mem_layer_of_quotient_eq k R R₀ hR)

end Erdos3.NilpotentLieFiltration

end

end OAI
