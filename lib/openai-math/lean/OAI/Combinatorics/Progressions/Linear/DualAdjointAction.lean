import OAI.Combinatorics.Progressions.Nilpotent.DualBCHDifferential

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[simp] theorem dualAdjoint_zero (g : NilpotentLieBCHGroup L s hnil) :
    dualAdjoint g 0 = 0 := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, dualTangentElement_zero, mul_one, mul_inv_cancel]

theorem dualAdjoint_add (g : NilpotentLieBCHGroup L s hnil) (x y : L) :
    dualAdjoint g (x + y) = dualAdjoint g x + dualAdjoint g y := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, ← dualTangentElement_mul, ← dualTangentElement_mul,
    ← dualAdjoint_spec, ← dualAdjoint_spec]
  group

@[simp] theorem dualAdjoint_neg (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g (-x) = -dualAdjoint g x := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, dualAdjoint_neg_spec]

theorem dualAdjoint_sub (g : NilpotentLieBCHGroup L s hnil) (x y : L) :
    dualAdjoint g (x - y) = dualAdjoint g x - dualAdjoint g y := by
  simp only [sub_eq_add_neg, dualAdjoint_add, dualAdjoint_neg]

@[simp] theorem dualAdjoint_one (x : L) :
    dualAdjoint (1 : NilpotentLieBCHGroup L s hnil) x = x := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, map_one, one_mul, inv_one, mul_one]

theorem dualAdjoint_mul (g h : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint (g * h) x = dualAdjoint g (dualAdjoint h x) := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, ← dualAdjoint_spec, ← dualAdjoint_spec, map_mul]
  group

@[simp] theorem dualAdjoint_inv_cancel (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g⁻¹ (dualAdjoint g x) = x := by
  rw [← dualAdjoint_mul, inv_mul_cancel, dualAdjoint_one]

@[simp] theorem dualAdjoint_cancel_inv (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g (dualAdjoint g⁻¹ x) = x := by
  rw [← dualAdjoint_mul, mul_inv_cancel, dualAdjoint_one]

theorem dualAdjoint_injective (g : NilpotentLieBCHGroup L s hnil) :
    Function.Injective (dualAdjoint g) := by
  intro x y h
  simpa only [dualAdjoint_inv_cancel] using congrArg (dualAdjoint g⁻¹) h

noncomputable def dualAdjointAddEquiv (g : NilpotentLieBCHGroup L s hnil) : L ≃+ L where
  toFun := dualAdjoint g
  invFun := dualAdjoint g⁻¹
  left_inv := dualAdjoint_inv_cancel g
  right_inv := dualAdjoint_cancel_inv g
  map_add' := dualAdjoint_add g

end Erdos3.NilpotentLieBCHGroup

end

end OAI
