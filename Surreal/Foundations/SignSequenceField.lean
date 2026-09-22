import Surreal.Foundations.SignSequenceGameAddition
import CombinatorialGames.Surreal.Division

/-!
# The ordered field on the sign carrier

The explicit sign/game equivalence preserves the previously constructed
Conway addition, sign reversal, zero and one. We use it to pull back the
proved upstream multiplication and division, retaining those existing
operations and the numerical order. This completes the ordered-field
structure in `found:sub:package` without postulating any field laws.

The genetic product-cut equation, real closedness and the Hahn normal-form
bridge are separate obligations.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Multiplication transported through the proved sign/game equivalence. -/
def mul (x y : SignSequence.{u}) : SignSequence.{u} :=
  toSurrealOrderIso.symm (toSurreal x * toSurreal y)

instance signSequenceMul : Mul SignSequence.{u} := ⟨mul⟩

@[simp] theorem toSurreal_mul (x y : SignSequence.{u}) :
    toSurreal (x * y) = toSurreal x * toSurreal y :=
  toSurreal_orderIso_symm _

/-- The ring structure extends the existing additive group with one. -/
instance signSequenceCommRing : CommRing SignSequence.{u} where
  __ := signSequenceAddCommGroupWithOne
  mul := (· * ·)
  mul_assoc x y z := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, _root_.mul_assoc]
  one_mul x := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, toSurreal_one, _root_.one_mul]
  mul_one x := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, toSurreal_one, _root_.mul_one]
  zero_mul x := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, toSurreal_zero, MulZeroClass.zero_mul]
  mul_zero x := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, toSurreal_zero, MulZeroClass.mul_zero]
  left_distrib x y z := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, toSurreal_add, _root_.mul_add]
  right_distrib x y z := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, toSurreal_add, _root_.add_mul]
  mul_comm x y := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_mul, _root_.mul_comm]

/-- Positive products agree with the previously fixed numerical order. -/
instance signSequenceIsStrictOrderedRing : IsStrictOrderedRing SignSequence.{u} :=
  .of_mul_pos (by
    intro x y hx hy
    apply (toSurreal_lt_iff _ _).mp
    rw [toSurreal_zero, toSurreal_mul]
    exact _root_.mul_pos
      (by simpa only [toSurreal_zero] using (toSurreal_lt_iff _ _).mpr hx)
      (by simpa only [toSurreal_zero] using (toSurreal_lt_iff _ _).mpr hy))

/-- The total inverse, including zero, transported from numeric games. -/
def inv (x : SignSequence.{u}) : SignSequence.{u} :=
  toSurrealOrderIso.symm (toSurreal x)⁻¹

instance signSequenceInv : Inv SignSequence.{u} := ⟨inv⟩

@[simp] theorem toSurreal_inv (x : SignSequence.{u}) :
    toSurreal x⁻¹ = (toSurreal x)⁻¹ := toSurreal_orderIso_symm _

/-- The actual sign carrier is a field, with no field axioms assumed. -/
instance signSequenceField : Field SignSequence.{u} where
  __ := signSequenceCommRing
  inv := Inv.inv
  mul_inv_cancel x hx := by
    apply (toSurreal_inj _ _).mp
    rw [toSurreal_mul, toSurreal_inv, toSurreal_one]
    apply _root_.mul_inv_cancel₀
    intro h
    apply hx
    apply (toSurreal_inj _ _).mp
    simpa only [toSurreal_zero] using h
  inv_zero := by
    apply (toSurreal_inj _ _).mp
    simp only [toSurreal_inv, toSurreal_zero, _root_.inv_zero]
  qsmul := _
  nnqsmul := _

/-- The same map is now an isomorphism of the actual fields. -/
def toSurrealRingEquiv : SignSequence.{u} ≃+* _root_.Surreal.{u} where
  toEquiv := toSurrealOrderIso.toEquiv
  map_add' := toSurreal_add
  map_mul' := toSurreal_mul

@[simp] theorem toSurrealRingEquiv_apply (x : SignSequence.{u}) :
    toSurrealRingEquiv x = toSurreal x := rfl

@[simp] theorem toSurreal_div (x y : SignSequence.{u}) :
    toSurreal (x / y) = toSurreal x / toSurreal y := by
  simp only [div_eq_mul_inv, toSurreal_mul, toSurreal_inv]

end

end Surreal.Foundations.SignSequence
