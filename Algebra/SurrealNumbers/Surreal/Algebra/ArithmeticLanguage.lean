import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Algebra.CharZero.Defs

/-!
# The common first-order language of natural and integer arithmetic

The literal signature `(0, 1, +, *)` in `odg:def:cor:arithmetic`, with its
usual interpretations on semirings and its inclusion in Mathlib's ring
language. Natural numbers form a substructure in this signature.
-/

namespace Surreal.StandardArithmetic
open FirstOrder FirstOrder.Language

/-- The four function symbols of the arithmetic signature. -/
inductive FunctionSymbol : ℕ → Type
  | zero : FunctionSymbol 0
  | one : FunctionSymbol 0
  | add : FunctionSymbol 2
  | mul : FunctionSymbol 2
  deriving DecidableEq

/-- The source's common signature for both standard arithmetic structures. -/
def language : Language where
  Functions := FunctionSymbol
  Relations := fun _ => Empty

instance arithmeticStructure (R : Type*) [Zero R] [One R] [Add R] [Mul R] : language.Structure R where
  funMap f x := match f with
    | .zero => 0
    | .one => 1
    | .add => x 0 + x 1
    | .mul => x 0 * x 1
  RelMap r := nomatch r

/-- The literal symbol inclusion into the first-order ring language. -/
def toRing : language →ᴸ Language.ring where
  onFunction _ f := match f with
    | .zero => .zero
    | .one => .one
    | .add => .add
    | .mul => .mul
  onRelation _ r := nomatch r

instance toRing_isExpansionOn (R : Type*) [Ring R] [FirstOrder.Ring.CompatibleRing R] :
    toRing.IsExpansionOn R where
  map_onFunction := by
    intro n f x
    cases f <;> simp [toRing] <;> rfl
  map_onRelation r := nomatch r

/-- Natural casts give a first-order embedding into every characteristic-zero semiring. -/
def naturalEmbedding (R : Type*) [Semiring R] [CharZero R] : ℕ ↪[language] R where
  toFun := Nat.cast
  inj' := Nat.cast_injective
  map_fun' := by
    intro n f x
    cases f with
    | zero => exact Nat.cast_zero
    | one => exact Nat.cast_one
    | add => exact Nat.cast_add _ _
    | mul => exact Nat.cast_mul _ _
  map_rel' r := nomatch r

end Surreal.StandardArithmetic
