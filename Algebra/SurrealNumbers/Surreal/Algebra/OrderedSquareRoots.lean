import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# The square-root hypothesis used by ordered quadratic geometry

The modulus and finite geometric identities need nonnegative square roots,
not the odd-degree polynomial root property of a real closed field.
This explicit property allows those proofs to be reused as soon as square
roots have been constructed on a concrete ordered field.
Real closed fields satisfy it by Mathlib's `IsSquare.of_nonneg`.
-/

namespace Surreal

/-- Every nonnegative element of this ordered field has a nonnegative
square root. This is a proved property when instantiated, not a new axiom. -/
class HasNonnegSquareRoots (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Prop where
  exists_nonneg_sq {x : F} : 0 ≤ x → ∃ y : F, 0 ≤ y ∧ y ^ 2 = x

instance hasNonnegSquareRoots_of_isRealClosed {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F] : HasNonnegSquareRoots F where
  exists_nonneg_sq hx := by
    obtain ⟨y, hy⟩ := IsSquare.of_nonneg hx
    exact ⟨|y|, abs_nonneg y, by simpa [pow_two] using hy.symm⟩

end Surreal
