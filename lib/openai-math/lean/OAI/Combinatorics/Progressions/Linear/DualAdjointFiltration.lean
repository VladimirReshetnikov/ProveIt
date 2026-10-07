import OAI.Combinatorics.Progressions.Linear.DualIdealSteps

namespace OAI


namespace Erdos3

namespace NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem map_dualAdjoint (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hL) (x : L) :
    φ (dualAdjoint g x) = dualAdjoint (map (hM := hM) φ g) (φ x) :=
  dualLinearLift_adjoint hM ⊤ φ φ.toLinearMap (fun a b _ => φ.map_lie a b) g x (by trivial)

theorem dualAdjoint_eq_self_of_lie_eq_zero (g : NilpotentLieBCHGroup L s hL) (x : L)
    (hgx : ⁅g.coord, x⁆ = 0) : dualAdjoint g x = x := by
  have hc : Commute (dualConstantHom g) (dualTangentElement x) := by
    apply commute_of_lie_eq_zero
    change ⁅dualConstantLie g.coord, dualInfinitesimal x⁆ = 0
    rw [dualConstant_infinitesimal_lie, hgx, map_zero]
  apply dualTangentElement_injective (hnil := hL)
  rw [← dualAdjoint_spec, hc.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem dualAdjoint_sub_mem_ideal (I : LieIdeal ℚ L) (g : NilpotentLieBCHGroup L s hL)
    (x : L) (hgx : ⁅g.coord, x⁆ ∈ I) : dualAdjoint g x - x ∈ I := by
  have hz : ⁅(quotientHom I g).coord, lieQuotientMap I x⁆ = 0 := by
    rw [quotientHom_coord, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hgx
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_dualAdjoint (hM := lie_quotient_lowerCentralSeries_eq_bot hL I)]
  exact sub_eq_zero.mpr (dualAdjoint_eq_self_of_lie_eq_zero (quotientHom I g) _ hz)

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualAdjoint_sub_mem_layer {i j : ℕ} (g : F.Group) (hg : g.coord ∈ F.layer i)
    (x : L) (hx : x ∈ F.layer j) : dualAdjoint g x - x ∈ F.layer (i + j) :=
  dualAdjoint_sub_mem_ideal (F.layerIdeal (i + j)) g x (F.lie_mem hg hx)

theorem dualAdjoint_mem_layer (j : ℕ) (g : F.Group) (x : L) (hx : x ∈ F.layer j) :
    dualAdjoint g x ∈ F.layer j := dualAdjoint_mem_ideal (F.layerIdeal j) g x hx

theorem dualAdjoint_sub_mem_next_layer (j : ℕ) (g : F.Group) (x : L) (hx : x ∈ F.layer j) :
    dualAdjoint g x - x ∈ F.layer (j + 1) := by
  have hg : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [Nat.add_comm 1 j] using F.dualAdjoint_sub_mem_layer g hg x hx

end NilpotentLieFiltration
end Erdos3

end OAI
