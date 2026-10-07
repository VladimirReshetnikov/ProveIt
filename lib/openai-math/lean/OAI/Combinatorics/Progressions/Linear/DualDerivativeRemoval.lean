import OAI.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket

namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_sub_tangent_mem (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (z : DualGroup hnil) (hb : dualBaseLinear z.coord ∈ U)
    (hbr : ⁅dualBaseLinear z.coord, dualTangentLinear z.coord⁆ ∈ V) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V := by
  let S := dualBaseSubalgebra U
  let I := dualInvariantTangentIdeal U V hUV
  let a : S := ⟨z.coord, ⟨hb, by trivial⟩⟩
  let b : S := ⟨-dualConstantLie (dualBaseLinear z.coord), by
    change dualBaseLinear (-dualConstantLie (dualBaseLinear z.coord)) ∈ U ∧ _
    constructor
    · rw [map_neg, dualBaseLinear_constant]
      exact U.neg_mem hb
    · trivial⟩
  have hab : ⁅a, b⁆ ∈ I := by
    change dualBaseLinear ⁅z.coord, -dualConstantLie (dualBaseLinear z.coord)⁆ = 0 ∧
      dualTangentLinear ⁅z.coord, -dualConstantLie (dualBaseLinear z.coord)⁆ ∈ V
    simp only [dualBaseLinear_lie, dualTangentLinear_lie, map_neg,
      dualBaseLinear_constant, dualTangentLinear_constant, neg_zero, lie_zero,
      zero_add, lie_neg, lie_self]
    rw [lie_skew]
    exact ⟨trivial, hbr⟩
  have he : lieBCH s a b - (a + b) ∈ I := by
    apply (lieQuotientMap_eq_zero I _).mp
    rw [map_sub, map_add, map_lieBCH]
    have hzero : ⁅lieQuotientMap I a, lieQuotientMap I b⁆ = 0 := by
      rw [← LieHom.map_lie]
      exact (lieQuotientMap_eq_zero I _).mpr hab
    rw [lieBCH_eq_add_of_lie_eq_zero_pos hs hzero, sub_self]
  have h := he.2
  change dualTangentLinear (S.incl (lieBCH s a b - (a + b))) ∈ V at h
  simp only [map_sub, map_add, map_lieBCH] at h
  change dualTangentLinear
      (lieBCH s z.coord (-dualConstantLie (dualBaseLinear z.coord))) -
    (dualTangentLinear z.coord +
      dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord))) ∈ V at h
  simp only [map_neg, dualTangentLinear_constant, neg_zero, add_zero] at h
  exact h

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualLogDerivative_sub_tangent_mem_layer (hs : 1 ≤ s) {i j : ℕ}
    (z : DualGroup F.lowerCentralSeries_eq_bot)
    (hb : dualBaseLinear z.coord ∈ F.layer i)
    (ht : dualTangentLinear z.coord ∈ F.layer j) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ F.layer (i + j) := by
  exact dualLogDerivative_sub_tangent_mem hs ⊤ (F.layerIdeal (i + j)).toSubmodule
    (fun _ _ _ hv => (F.layerIdeal _).lie_mem hv) z (by trivial) (F.lie_mem hb ht)

theorem logDerivative_current_layer_relation (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hb : dualBaseLinear z.coord ∈ U)
    (hbr : ⁅dualBaseLinear z.coord, dualTangentLinear z.coord⁆ ∈ V ⊔ F.layer (j + 1)) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V ⊔ F.layer (j + 1) :=
  dualLogDerivative_sub_tangent_mem hs U (V ⊔ F.layer (j + 1))
    (F.invariant_sup_layer U V hUV (j + 1)) z hb hbr

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[simp] theorem dualLogDerivative_one : dualLogDerivative (1 : DualGroup hnil) = 0 := by
  simp only [dualLogDerivative, map_one, inv_one, mul_one, coord_one, map_zero]

theorem dualLogDerivative_inv (z : DualGroup hnil) :
    dualLogDerivative z⁻¹ = -dualAdjoint (dualBaseHom z)⁻¹ (dualLogDerivative z) := by
  have h := dualLogDerivative_mul z z⁻¹
  rw [mul_inv_cancel, dualLogDerivative_one] at h
  have he := congrArg (dualAdjoint (dualBaseHom z)⁻¹) h
  rw [dualAdjoint_zero, dualAdjoint_add, dualAdjoint_inv_cancel] at he
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using he.symm

theorem dualLogDerivative_remove (a z c : DualGroup hnil) :
    dualLogDerivative (a⁻¹ * z * c⁻¹) =
      dualAdjoint (dualBaseHom a)⁻¹ (dualLogDerivative z - dualLogDerivative a) -
        dualAdjoint (dualBaseHom (a⁻¹ * z * c⁻¹)) (dualLogDerivative c) := by
  simp only [dualLogDerivative_mul, dualLogDerivative_inv, map_mul, map_inv,
    dualAdjoint_mul, dualAdjoint_neg, dualAdjoint_sub]
  abel

theorem dualDerivativeSystem_remove (a z c : DualGroup hnil) (small rational extra : L)
    (hsystem : dualLogDerivative z = small + dualAdjoint (dualBaseHom z) rational + extra) :
    dualLogDerivative (a⁻¹ * z * c⁻¹) =
      dualAdjoint (dualBaseHom a)⁻¹ (small - dualLogDerivative a) +
        dualAdjoint (dualBaseHom (a⁻¹ * z * c⁻¹))
          (dualAdjoint (dualBaseHom c) rational - dualLogDerivative c) +
        dualAdjoint (dualBaseHom a)⁻¹ extra := by
  rw [dualLogDerivative_remove, hsystem]
  simp only [map_mul, map_inv, dualAdjoint_mul, dualAdjoint_add, dualAdjoint_sub,
    dualAdjoint_inv_cancel]
  abel

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem derivative_removal_preserves_quotient_layers
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (a c : DualGroup F.lowerCentralSeries_eq_bot)
    (haU : dualBaseLinear a.coord ∈ U) (hcU : dualBaseLinear c.coord ∈ U)
    (haV : dualTangentLinear a.coord ∈ V) (hcV : dualTangentLinear c.coord ∈ V)
    (small rational : L) (hsmall : small ∈ V ⊔ F.layer j)
    (hrational : rational ∈ V ⊔ F.layer j) :
    dualAdjoint (dualBaseHom a)⁻¹ (small - dualLogDerivative a) ∈ V ⊔ F.layer j ∧
      dualAdjoint (dualBaseHom c) rational - dualLogDerivative c ∈ V ⊔ F.layer j := by
  have hYa := dualLogDerivative_mem_of_invariant U V hUV a haU haV
  have hYc := dualLogDerivative_mem_of_invariant U V hUV c hcU hcV
  have hW := F.invariant_sup_layer U V hUV j
  constructor
  · apply dualAdjoint_mem_of_invariant U (V ⊔ F.layer j) hW _ (U.neg_mem haU)
    exact (V ⊔ F.layer j).sub_mem hsmall (Submodule.mem_sup_left hYa)
  · exact (V ⊔ F.layer j).sub_mem
      (dualAdjoint_mem_of_invariant U (V ⊔ F.layer j) hW _ hcU rational hrational)
      (Submodule.mem_sup_left hYc)

end NilpotentLieFiltration
end Erdos3

end

end OAI
