import Surreal.Foundations.SignSequenceAddAssociative
import Surreal.Foundations.SignSequenceAddInverse
import Mathlib.Algebra.Order.Group.Defs

/-!
# The ordered additive group of canonical signs

The certified Conway addition, associativity, zero laws and sign-reversal
inverse laws assemble into Mathlib's native additive commutative group.
Strict translation preserves the previously constructed numerical order.
Multiplication, field inverses and the normal-form bridge are separate
constructions and are not assumed by these instances.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The concrete group uses the recursive addition and the original sign
reversal; no group law is postulated. -/
instance signSequenceAddCommGroup : AddCommGroup SignSequence.{u} where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The additive structure respects the original first-disagreement order. -/
instance signSequenceIsOrderedAddMonoid : IsOrderedAddMonoid SignSequence.{u} where
  add_le_add_left _ _ h c := (add_right_strictMono c).monotone h

end

end Surreal.Foundations.SignSequence
