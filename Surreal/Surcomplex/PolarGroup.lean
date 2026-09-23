import Surreal.Surcomplex.AngleGroup

/-!
# Multiplicative polar decomposition of the actual surcomplex field

The positive modulus and unit direction give the group isomorphism in
`trigonometry:prop:rotation`. Combining it with the finite-angle quotient
completes the corresponding quotient form of `trigonometry:thm:polar`.
No finiteness assumption is placed on the modulus or the original input.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Positive actual real units, with their native multiplicative subgroup structure. -/
def positiveUnitSubgroup : Subgroup SignSequence.{u}ˣ where
  carrier := {r | 0 < (r : SignSequence.{u})}
  one_mem' := by change (0 : SignSequence.{u}) < 1; exact zero_lt_one
  mul_mem' {r s} hr hs := by
    change 0 < (r : SignSequence.{u}) at hr
    change 0 < (s : SignSequence.{u}) at hs
    change 0 < (r : SignSequence.{u}) * (s : SignSequence.{u})
    exact mul_pos hr hs
  inv_mem' := by
    intro r hr
    change 0 < (r : SignSequence.{u}) at hr
    change 0 < ((r⁻¹ : SignSequence.{u}ˣ) : SignSequence.{u})
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hr

/-- Multiplication of a positive modulus and a unit direction. -/
def polarMultiply : positiveUnitSubgroup.{u} × UnitCircle.{u} →* Surcomplex.{u}ˣ where
  toFun p := Units.mk0 (ofReal (p.1.val : SignSequence.{u}) * p.2.val)
    (mul_ne_zero ((map_ne_zero ofReal).mpr p.1.val.ne_zero) (Unitary.isUnit_coe.ne_zero))
  map_one' := by apply Units.ext; simp
  map_mul' p q := by
    apply Units.ext
    change ofReal ((p.1.val : SignSequence.{u}) * (q.1.val : SignSequence.{u})) *
      (p.2.val * q.2.val) =
      (ofReal (p.1.val : SignSequence.{u}) * p.2.val) *
        (ofReal (q.1.val : SignSequence.{u}) * q.2.val)
    rw [map_mul]
    ring

@[simp] theorem coe_polarMultiply (p : positiveUnitSubgroup.{u} × UnitCircle.{u}) :
    (polarMultiply p : Surcomplex.{u}) = ofReal (p.1.val : SignSequence.{u}) * p.2.val := rfl

/-- The positive factor is necessarily the actual modulus. -/
@[simp] theorem modulus_polarMultiply (p : positiveUnitSubgroup.{u} × UnitCircle.{u}) :
    modulus (polarMultiply p : Surcomplex.{u}) = (p.1.val : SignSequence.{u}) := by
  rw [coe_polarMultiply, modulus_mul, modulus_ofReal, modulus_unitCircle, mul_one,
    abs_of_pos p.1.property]

/-- Positive modulus and unit direction are jointly unique. -/
theorem polarMultiply_injective : Function.Injective polarMultiply.{u} := by
  intro p q h
  have hr := congrArg (fun z : Surcomplex.{u}ˣ => modulus z) h
  simp only [modulus_polarMultiply] at hr
  have hp : p.1 = q.1 := Subtype.ext (Units.ext hr)
  apply Prod.ext hp
  apply Subtype.ext
  have he := congrArg (fun z : Surcomplex.{u}ˣ => (z : Surcomplex.{u})) h
  simp only [coe_polarMultiply] at he
  rw [hr] at he
  exact mul_left_cancel₀ ((map_ne_zero ofReal).mpr q.1.val.ne_zero) he

/-- Polar multiplication covers nonzero inputs of every actual size. -/
theorem polarMultiply_surjective : Function.Surjective polarMultiply.{u} := by
  intro z
  have hr := modulus_pos z.ne_zero
  obtain ⟨θ, hθ⟩ := exists_polar z z.ne_zero
  let r : positiveUnitSubgroup.{u} := ⟨Units.mk0 (modulus z) hr.ne', hr⟩
  refine ⟨(r, finitePhaseHom (Multiplicative.ofAdd θ)), ?_⟩
  apply Units.ext
  exact hθ.symm

/-- The multiplicative polar group is the product of positive reals and unit directions. -/
def polarGroupEquiv : positiveUnitSubgroup.{u} × UnitCircle.{u} ≃* Surcomplex.{u}ˣ :=
  MulEquiv.ofBijective polarMultiply ⟨polarMultiply_injective, polarMultiply_surjective⟩

@[simp] theorem polarGroupEquiv_apply (p : positiveUnitSubgroup.{u} × UnitCircle.{u}) :
    polarGroupEquiv p = polarMultiply p := rfl

/-- The inverse polar isomorphism extracts the actual positive modulus. -/
@[simp] theorem polarGroupEquiv_symm_fst (z : Surcomplex.{u}ˣ) :
    ((polarGroupEquiv.symm z).1.val : SignSequence.{u}) = modulus z := by
  have h := modulus_polarMultiply (polarGroupEquiv.symm z)
  rw [← polarGroupEquiv_apply, polarGroupEquiv.apply_symm_apply] at h
  exact h.symm

/-- The inverse polar isomorphism extracts division by that modulus. -/
@[simp] theorem polarGroupEquiv_symm_snd (z : Surcomplex.{u}ˣ) :
    (polarGroupEquiv.symm z).2.val = (z : Surcomplex.{u}) / ofReal (modulus z) := by
  have h := congrArg (fun w : Surcomplex.{u}ˣ => (w : Surcomplex.{u}))
    (polarGroupEquiv.apply_symm_apply z)
  rw [polarGroupEquiv_apply, coe_polarMultiply, polarGroupEquiv_symm_fst] at h
  apply (eq_div_iff ((map_ne_zero ofReal).mpr (modulus_pos z.ne_zero).ne')).mpr
  simpa only [mul_comm] using h

/-- Branch-free polar decomposition with a finite-angle class instead of a unit direction. -/
def polarAngleGroupEquiv :
    positiveUnitSubgroup.{u} × (Multiplicative SignSequence.FiniteElement.{u} ⧸ anglePeriods) ≃*
      Surcomplex.{u}ˣ :=
  (MulEquiv.prodCongr (MulEquiv.refl _) angleQuotientEquiv).trans polarGroupEquiv

/-- The quotient polar map is exactly radius times phase on an angle representative. -/
@[simp] theorem polarAngleGroupEquiv_mk (r : positiveUnitSubgroup.{u})
    (θ : Multiplicative SignSequence.FiniteElement.{u}) :
    (polarAngleGroupEquiv (r, QuotientGroup.mk θ) : Surcomplex.{u}) =
      ofReal (r.val : SignSequence.{u}) * finitePhase θ.toAdd := rfl

/-- The angle-class polar product still has the specified positive modulus. -/
theorem modulus_polarAngleGroupEquiv
    (p : positiveUnitSubgroup.{u} ×
      (Multiplicative SignSequence.FiniteElement.{u} ⧸ anglePeriods)) :
    modulus (polarAngleGroupEquiv p : Surcomplex.{u}) = (p.1.val : SignSequence.{u}) :=
  modulus_polarMultiply (p.1, angleQuotientEquiv p.2)

/-- Every nonzero actual surcomplex has exactly one positive modulus and finite angle class. -/
theorem existsUnique_polar_angleClass (z : Surcomplex.{u}) (hz : z ≠ 0) :
    ∃! p : positiveUnitSubgroup.{u} ×
      (Multiplicative SignSequence.FiniteElement.{u} ⧸ anglePeriods),
      (polarAngleGroupEquiv p : Surcomplex.{u}) = z := by
  refine ⟨polarAngleGroupEquiv.symm (Units.mk0 z hz), ?_, ?_⟩
  · exact congrArg (fun w : Surcomplex.{u}ˣ => (w : Surcomplex.{u}))
      (polarAngleGroupEquiv.apply_symm_apply (Units.mk0 z hz))
  · intro p hp
    apply polarAngleGroupEquiv.injective
    rw [polarAngleGroupEquiv.apply_symm_apply]
    exact Units.ext hp

end
end Surreal.Surcomplex
