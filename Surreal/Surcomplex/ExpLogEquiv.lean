import Surreal.Foundations.SignSequenceExpLog
import Surreal.Surcomplex.ExpLog

/-!
# Actual infinitesimal exponential group equivalences

For both actual surreal and surcomplex numbers, infinitesimal exponential
is a multiplicative group equivalence from the additive infinitesimals to
the units differing infinitesimally from one. Its inverse is the strong
logarithm of that unit. Closure of the target follows from the already
proved exponential identities, with no global exponential assumption.
This bundles the isomorphism clause of `e:prop-infexp` literally.
-/

universe u

noncomputable section

namespace Surreal.Foundations.SignSequence

/-- The actual units infinitesimally close to one form a multiplicative subgroup. -/
def infinitesimalUnitSubgroup : Subgroup SignSequence.{u}ˣ where
  carrier := {z | IsInfinitesimal ((z : SignSequence.{u}) - 1)}
  one_mem' := by
    change IsInfinitesimal ((1 : SignSequence.{u}) - 1)
    simpa only [sub_self] using (infinitesimal_zero : IsInfinitesimal (0 : SignSequence.{u}))
  mul_mem' {x y} hx hy := by
    change IsInfinitesimal ((x : SignSequence.{u}) * (y : SignSequence.{u}) - 1)
    simpa only [add_sub_cancel] using
      infinitesimal_one_add_mul_sub_one ((x : SignSequence.{u}) - 1) ((y : SignSequence.{u}) - 1) hx hy
  inv_mem' {x} hx := by
    change IsInfinitesimal ((↑(x⁻¹) : SignSequence.{u}) - 1)
    have hl := infinitesimal_infLog ((x : SignSequence.{u}) - 1) hx
    have hn : IsInfinitesimal (-infLog ((x : SignSequence.{u}) - 1) hx) :=
      infinitesimalAddSubgroup.neg_mem hl
    have h := infinitesimal_infExp_sub_one (-infLog ((x : SignSequence.{u}) - 1) hx) hn
    simpa only [infExp_neg _ hl, infExp_infLog, add_sub_cancel,
      Units.val_inv_eq_inv_val] using h

@[simp] theorem mem_infinitesimalUnitSubgroup (z : SignSequence.{u}ˣ) :
    z ∈ infinitesimalUnitSubgroup ↔ IsInfinitesimal ((z : SignSequence.{u}) - 1) := Iff.rfl

/-- Actual strong exponential and logarithm are inverse group isomorphisms at zero and one. -/
def infExpEquiv : Multiplicative infinitesimalAddSubgroup.{u} ≃*
    infinitesimalUnitSubgroup.{u} where
  toFun x := ⟨Units.mk0 (infExp x.toAdd.val x.toAdd.property)
    (infExp_ne_zero x.toAdd.val x.toAdd.property),
    infinitesimal_infExp_sub_one x.toAdd.val x.toAdd.property⟩
  invFun z := Multiplicative.ofAdd
    ⟨infLog ((z.val : SignSequence.{u}) - 1) z.property, infinitesimal_infLog _ _⟩
  left_inv x := by
    apply Subtype.ext
    exact infLog_infExp_sub_one x.toAdd.val x.toAdd.property
  right_inv z := by
    apply Subtype.ext
    apply Units.ext
    change infExp (infLog ((z.val : SignSequence.{u}) - 1) z.property) _ = (z.val : SignSequence.{u})
    rw [infExp_infLog, add_sub_cancel]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact infExp_add x.toAdd.val y.toAdd.val x.toAdd.property y.toAdd.property

@[simp] theorem infExpEquiv_apply (x : Multiplicative infinitesimalAddSubgroup.{u}) :
    ((infExpEquiv x).val : SignSequence.{u}) = infExp x.toAdd.val x.toAdd.property := rfl

@[simp] theorem infExpEquiv_symm_apply (z : infinitesimalUnitSubgroup.{u}) :
    (infExpEquiv.symm z).toAdd.val = infLog ((z.val : SignSequence.{u}) - 1) z.property := rfl

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

/-- The coordinatewise actual surcomplex infinitesimals form an additive subgroup. -/
def infinitesimalAddSubgroup : AddSubgroup Surcomplex.{u} where
  carrier := {z | IsInfinitesimal z}
  zero_mem' := ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩
  add_mem' hx hy :=
    ⟨SignSequence.infinitesimal_add hx.1 hy.1, SignSequence.infinitesimal_add hx.2 hy.2⟩
  neg_mem' hx := ⟨SignSequence.infinitesimal_neg hx.1, SignSequence.infinitesimal_neg hx.2⟩

@[simp] theorem mem_infinitesimalAddSubgroup (z : Surcomplex.{u}) :
    z ∈ infinitesimalAddSubgroup ↔ IsInfinitesimal z := Iff.rfl

/-- The actual units infinitesimally close to one form a multiplicative subgroup. -/
def infinitesimalUnitSubgroup : Subgroup Surcomplex.{u}ˣ where
  carrier := {z | IsInfinitesimal ((z : Surcomplex.{u}) - 1)}
  one_mem' := by
    change IsInfinitesimal ((1 : Surcomplex.{u}) - 1)
    simpa only [sub_self] using (show IsInfinitesimal (0 : Surcomplex.{u}) from
      ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩)
  mul_mem' {x y} hx hy := by
    change IsInfinitesimal ((x : Surcomplex.{u}) * (y : Surcomplex.{u}) - 1)
    simpa only [add_sub_cancel] using
      infinitesimal_one_add_mul_sub_one ((x : Surcomplex.{u}) - 1) ((y : Surcomplex.{u}) - 1) hx hy
  inv_mem' {x} hx := by
    change IsInfinitesimal ((↑(x⁻¹) : Surcomplex.{u}) - 1)
    have hl := infinitesimal_infLog ((x : Surcomplex.{u}) - 1) hx
    have hn : IsInfinitesimal (-infLog ((x : Surcomplex.{u}) - 1) hx) :=
      infinitesimalAddSubgroup.neg_mem hl
    have h := infinitesimal_infExp_sub_one (-infLog ((x : Surcomplex.{u}) - 1) hx) hn
    simpa only [infExp_neg _ hl, infExp_infLog, add_sub_cancel,
      Units.val_inv_eq_inv_val] using h

@[simp] theorem mem_infinitesimalUnitSubgroup (z : Surcomplex.{u}ˣ) :
    z ∈ infinitesimalUnitSubgroup ↔ IsInfinitesimal ((z : Surcomplex.{u}) - 1) := Iff.rfl

/-- Actual strong exponential and logarithm are inverse group isomorphisms at zero and one. -/
def infExpEquiv : Multiplicative infinitesimalAddSubgroup.{u} ≃*
    infinitesimalUnitSubgroup.{u} where
  toFun x := ⟨Units.mk0 (infExp x.toAdd.val x.toAdd.property)
    (infExp_ne_zero x.toAdd.val x.toAdd.property),
    infinitesimal_infExp_sub_one x.toAdd.val x.toAdd.property⟩
  invFun z := Multiplicative.ofAdd
    ⟨infLog ((z.val : Surcomplex.{u}) - 1) z.property, infinitesimal_infLog _ _⟩
  left_inv x := by
    apply Subtype.ext
    exact infLog_infExp_sub_one x.toAdd.val x.toAdd.property
  right_inv z := by
    apply Subtype.ext
    apply Units.ext
    change infExp (infLog ((z.val : Surcomplex.{u}) - 1) z.property) _ = (z.val : Surcomplex.{u})
    rw [infExp_infLog, add_sub_cancel]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact infExp_add x.toAdd.val y.toAdd.val x.toAdd.property y.toAdd.property

@[simp] theorem infExpEquiv_apply (x : Multiplicative infinitesimalAddSubgroup.{u}) :
    ((infExpEquiv x).val : Surcomplex.{u}) = infExp x.toAdd.val x.toAdd.property := rfl

@[simp] theorem infExpEquiv_symm_apply (z : infinitesimalUnitSubgroup.{u}) :
    (infExpEquiv.symm z).toAdd.val = infLog ((z.val : Surcomplex.{u}) - 1) z.property := rfl

end Surreal.Surcomplex

end
