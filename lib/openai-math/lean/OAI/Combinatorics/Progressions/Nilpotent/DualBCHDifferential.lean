import Mathlib.Tactic.Group
import OAI.Combinatorics.Progressions.Linear.DualLieAlgebra

namespace OAI


namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

abbrev DualGroup (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :=
  NilpotentLieBCHGroup (DualLieAlgebra L) s (dualLie_lowerCentralSeries_eq_bot hnil)

noncomputable def dualConstantHom : NilpotentLieBCHGroup L s hnil →* DualGroup hnil :=
  map dualConstantLie

noncomputable def dualBaseHom : DualGroup hnil →* NilpotentLieBCHGroup L s hnil :=
  map dualBaseLie

noncomputable def dualTangentElement (x : L) : DualGroup hnil := ⟨dualInfinitesimal x⟩

@[simp] theorem dualBaseHom_constant (g : NilpotentLieBCHGroup L s hnil) :
    dualBaseHom (dualConstantHom g) = g := by
  apply ext
  exact dualBaseLinear_constant g.coord

@[simp] theorem dualBaseHom_tangent (x : L) :
    dualBaseHom (dualTangentElement (hnil := hnil) x) = 1 := by
  apply ext
  exact dualBaseLinear_infinitesimal x

theorem dualTangentElement_injective : Function.Injective (dualTangentElement (hnil := hnil)) := by
  intro x y h
  exact dualInfinitesimal_injective (congrArg coord h)

@[simp] theorem dualTangentElement_zero : dualTangentElement (hnil := hnil) (0 : L) = 1 := by
  apply ext
  exact map_zero dualInfinitesimal

theorem dualTangentElement_mul (x y : L) :
    dualTangentElement (hnil := hnil) x * dualTangentElement y = dualTangentElement (x + y) := by
  apply ext
  change lieBCH s (dualInfinitesimal x) (dualInfinitesimal y) = dualInfinitesimal (x + y)
  rw [lieBCH_eq_add_of_lie_eq_zero (dualLie_lowerCentralSeries_eq_bot hnil) (dualInfinitesimal_lie x y),
    map_add]

theorem dualTangentElement_neg (x : L) :
    dualTangentElement (hnil := hnil) (-x) = (dualTangentElement x)⁻¹ := by
  apply ext
  exact map_neg dualInfinitesimal x

theorem dualBaseHom_eq_one_iff (g : DualGroup hnil) :
    dualBaseHom g = 1 ↔ g = dualTangentElement (dualTangentLinear g.coord) := by
  constructor
  · intro hg
    have hb : dualBaseLinear g.coord = 0 := congrArg coord hg
    apply ext
    change g.coord = dualInfinitesimal (dualTangentLinear g.coord)
    conv_lhs => rw [dualLie_decomposition g.coord, hb, map_zero, zero_add]
  · intro hg
    rw [hg, dualBaseHom_tangent]

end Erdos3.NilpotentLieBCHGroup


namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def dualAdjoint (g : NilpotentLieBCHGroup L s hnil) (x : L) : L :=
  dualTangentLinear
    (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹).coord

theorem dualAdjoint_spec (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹ =
      dualTangentElement (dualAdjoint g x) := by
  apply (dualBaseHom_eq_one_iff _).mp
  simp only [map_mul, map_inv, dualBaseHom_constant, dualBaseHom_tangent, mul_one, mul_inv_cancel]

theorem dualAdjoint_neg_spec (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualConstantHom g * dualTangentElement (-x) * (dualConstantHom g)⁻¹ =
      dualTangentElement (-dualAdjoint g x) := by
  calc
    _ = (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹)⁻¹ := by
      rw [dualTangentElement_neg]
      group
    _ = _ := by rw [dualAdjoint_spec, dualTangentElement_neg]

noncomputable def dualLogDerivative (z : DualGroup hnil) : L :=
  dualTangentLinear (z * (dualConstantHom (dualBaseHom z))⁻¹).coord

theorem dualLogDerivative_spec (z : DualGroup hnil) :
    z * (dualConstantHom (dualBaseHom z))⁻¹ = dualTangentElement (dualLogDerivative z) := by
  apply (dualBaseHom_eq_one_iff _).mp
  simp only [map_mul, map_inv, dualBaseHom_constant, mul_inv_cancel]

theorem dualLogDerivative_factorization (z : DualGroup hnil) :
    z = dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z) := by
  calc
    _ = (z * (dualConstantHom (dualBaseHom z))⁻¹) * dualConstantHom (dualBaseHom z) := by group
    _ = _ := by rw [dualLogDerivative_spec]

theorem dualLogDerivative_tangent_mul_constant (x : L) (g : NilpotentLieBCHGroup L s hnil) :
    dualLogDerivative (dualTangentElement x * dualConstantHom g) = x := by
  simp only [dualLogDerivative, map_mul, dualBaseHom_tangent, dualBaseHom_constant, one_mul,
    mul_inv_cancel_right]
  exact dualTangentLinear_infinitesimal x

theorem dualLogDerivative_mul (z w : DualGroup hnil) :
    dualLogDerivative (z * w) = dualLogDerivative z + dualAdjoint (dualBaseHom z) (dualLogDerivative w) := by
  have h : z * w =
      dualTangentElement (dualLogDerivative z + dualAdjoint (dualBaseHom z) (dualLogDerivative w)) *
        dualConstantHom (dualBaseHom z * dualBaseHom w) := by
    calc
      _ = (dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z)) *
          (dualTangentElement (dualLogDerivative w) * dualConstantHom (dualBaseHom w)) :=
        congrArg₂ (· * ·) (dualLogDerivative_factorization z) (dualLogDerivative_factorization w)
      _ = dualTangentElement (dualLogDerivative z) *
          (dualConstantHom (dualBaseHom z) * dualTangentElement (dualLogDerivative w) *
            (dualConstantHom (dualBaseHom z))⁻¹) *
          (dualConstantHom (dualBaseHom z) * dualConstantHom (dualBaseHom w)) := by group
      _ = _ := by rw [dualAdjoint_spec, dualTangentElement_mul, map_mul]
  rw [h, dualLogDerivative_tangent_mul_constant]

theorem dualBCH_insertion_identity (z : DualGroup hnil) (e m : L) :
    dualTangentElement (-e) * z * dualTangentElement (-m) *
        (dualConstantHom (dualBaseHom z))⁻¹ =
      dualTangentElement (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m) := by
  calc
    _ = dualTangentElement (-e) *
        (dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z)) *
        dualTangentElement (-m) * (dualConstantHom (dualBaseHom z))⁻¹ :=
      congrArg (fun a => dualTangentElement (-e) * a * dualTangentElement (-m) *
        (dualConstantHom (dualBaseHom z))⁻¹) (dualLogDerivative_factorization z)
    _ = dualTangentElement (-e) * dualTangentElement (dualLogDerivative z) *
        (dualConstantHom (dualBaseHom z) * dualTangentElement (-m) *
          (dualConstantHom (dualBaseHom z))⁻¹) := by group
    _ = dualTangentElement (-e + dualLogDerivative z + -dualAdjoint (dualBaseHom z) m) := by
      rw [dualAdjoint_neg_spec, dualTangentElement_mul, dualTangentElement_mul]
    _ = _ := by congr 1; abel

end Erdos3.NilpotentLieBCHGroup

end OAI
