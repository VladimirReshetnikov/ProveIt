/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.DualNumber
import OAI.Combinatorics.Progressions.Estimates.RealifiedMultidegree

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

abbrev DualLieAlgebra (L : Type*) [LieRing L] [LieAlgebra ℚ L] := DualNumber ℚ ⊗[ℚ] L

noncomputable def dualBaseLinear : DualLieAlgebra L →ₗ[ℚ] L :=
  (TensorProduct.lid ℚ L).toLinearMap.comp
    ((TrivSqZeroExt.fstHom ℚ ℚ ℚ).toLinearMap.rTensor L)

noncomputable def dualTangentLinear : DualLieAlgebra L →ₗ[ℚ] L :=
  (TensorProduct.lid ℚ L).toLinearMap.comp ((TrivSqZeroExt.sndHom ℚ ℚ).rTensor L)

@[simp] theorem dualBaseLinear_tmul (r : DualNumber ℚ) (x : L) :
    dualBaseLinear (r ⊗ₜ[ℚ] x) = r.fst • x := rfl

@[simp] theorem dualTangentLinear_tmul (r : DualNumber ℚ) (x : L) :
    dualTangentLinear (r ⊗ₜ[ℚ] x) = r.snd • x := rfl

noncomputable def dualConstantLie : L →ₗ⁅ℚ⁆ DualLieAlgebra L where
  toLinearMap := TensorProduct.mk ℚ (DualNumber ℚ) L 1
  map_lie' {x y} := by simp [LieAlgebra.ExtendScalars.bracket_tmul]

noncomputable def dualInfinitesimal : L →ₗ[ℚ] DualLieAlgebra L :=
  TensorProduct.mk ℚ (DualNumber ℚ) L DualNumber.eps

@[simp] theorem dualBaseLinear_constant (x : L) : dualBaseLinear (dualConstantLie x) = x := by
  change (1 : ℚ) • x = x
  exact one_smul ℚ x

@[simp] theorem dualTangentLinear_constant (x : L) : dualTangentLinear (dualConstantLie x) = 0 := by
  change (0 : ℚ) • x = 0
  exact zero_smul ℚ x

@[simp] theorem dualBaseLinear_infinitesimal (x : L) : dualBaseLinear (dualInfinitesimal x) = 0 := by
  change (0 : ℚ) • x = 0
  exact zero_smul ℚ x

@[simp] theorem dualTangentLinear_infinitesimal (x : L) : dualTangentLinear (dualInfinitesimal x) = x := by
  change (1 : ℚ) • x = x
  exact one_smul ℚ x

theorem dualInfinitesimal_injective : Function.Injective (dualInfinitesimal (L := L)) := by
  intro x y h
  simpa only [dualTangentLinear_infinitesimal] using congrArg dualTangentLinear h

theorem dualLie_decomposition (z : DualLieAlgebra L) :
    z = dualConstantLie (dualBaseLinear z) + dualInfinitesimal (dualTangentLinear z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    have hr : r = r.fst • (1 : DualNumber ℚ) + r.snd • DualNumber.eps := by
      ext <;> simp
    change r ⊗ₜ[ℚ] x = (1 : DualNumber ℚ) ⊗ₜ[ℚ] (r.fst • x) +
      DualNumber.eps ⊗ₜ[ℚ] (r.snd • x)
    calc
      _ = (r.fst • (1 : DualNumber ℚ) + r.snd • DualNumber.eps) ⊗ₜ[ℚ] x :=
        congrArg (fun a : DualNumber ℚ => a ⊗ₜ[ℚ] x) hr
      _ = _ := by rw [TensorProduct.add_tmul]; simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add x y hx hy =>
    calc
      _ = (dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x)) +
          (dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y)) :=
        congrArg₂ (· + ·) hx hy
      _ = _ := by simp only [map_add]; abel

private theorem ring_zero_lie {K : Type*} [LieRing K] (x : K) : ⁅(0 : K), x⁆ = 0 := zero_lie x
private theorem ring_lie_zero {K : Type*} [LieRing K] (x : K) : ⁅x, (0 : K)⁆ = 0 := lie_zero x

theorem dualBaseLinear_lie (x y : DualLieAlgebra L) :
    dualBaseLinear ⁅x, y⁆ = ⁅dualBaseLinear x, dualBaseLinear y⁆ := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    induction y using TensorProduct.inductionOn with
    | tmul q y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, dualBaseLinear_tmul,
        TrivSqZeroExt.fst_mul, smul_lie, lie_smul, smul_smul, mul_comm]
    | add y z hy hz =>
      rw [LieRing.lie_add (r ⊗ₜ[ℚ] x) y z, map_add, hy, hz, map_add, LieRing.lie_add]
  | add x z hx hz => rw [LieRing.add_lie x z y, map_add, hx, hz, map_add, LieRing.add_lie]

noncomputable def dualBaseLie : DualLieAlgebra L →ₗ⁅ℚ⁆ L where
  toLinearMap := dualBaseLinear
  map_lie' {x y} := dualBaseLinear_lie x y

theorem dualInfinitesimal_lie (x y : L) : ⁅dualInfinitesimal x, dualInfinitesimal y⁆ = 0 := by
  change ⁅DualNumber.eps ⊗ₜ[ℚ] x, DualNumber.eps ⊗ₜ[ℚ] y⁆ = 0
  rw [LieAlgebra.ExtendScalars.bracket_tmul, DualNumber.eps_mul_eps, TensorProduct.zero_tmul]

theorem dualLie_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (DualLieAlgebra L) (DualLieAlgebra L) s = ⊥ := by
  have hdual : LieModule.lowerCentralSeries (DualNumber ℚ) (DualLieAlgebra L) (DualLieAlgebra L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (DualLieAlgebra L) (DualLieAlgebra L) s : Set (DualLieAlgebra L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int (DualNumber ℚ) (DualLieAlgebra L) (DualLieAlgebra L) s,
    hdual]
  rfl

end Erdos3

end

end OAI
