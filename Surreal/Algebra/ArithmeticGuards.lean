import Surreal.Algebra.DiophantineConstants
import Surreal.Algebra.NaturalNumbersDefinition
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.ModelTheory.Definability

/-!
# Native first-order guards for ordinary integer and natural constants

The formulas used to relativize arithmetic in `odg:def:cor:arithmetic`.
The integer guard is exactly `odg:def:eq:system`, with five witnesses.
The natural guard adds the four squares of `odg:def:cor:naturals`.
All syntax is constructed explicitly using only the ring language.
-/

namespace Surreal.ArithmeticGuards
open FirstOrder FirstOrder.Language

/-- A numeral built by finite recursion from zero, one and addition. -/
def numeral {α : Type*} : ℕ → Language.ring.Term α
  | 0 => 0
  | n + 1 => numeral n + 1

variable {R : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]

@[simp] theorem realize_numeral {α : Type*} (n : ℕ) (v : α → R) :
    (numeral n).realize v = (n : R) := by
  induction n with
  | zero => simp [numeral]
  | succ n ih => simp [numeral, ih, Nat.cast_add, Nat.cast_one]

/-- The intersective polynomial expressed as a native ring term. -/
def certificate {α : Type*} (t : Language.ring.Term α) : Language.ring.Term α :=
  ((t * t + -numeral 13) * (t * t + -numeral 17)) * (t * t + -numeral 221)

@[simp] theorem realize_certificate {α : Type*} (t : Language.ring.Term α) (v : α → R) :
    (certificate t).realize v = IntersectivePolynomial.value (t.realize v) := by
  simp [certificate, IntersectivePolynomial.value, pow_two, sub_eq_add_neg]

/-- The three equations, with one free variable and five bound witnesses. -/
def integerSystem : Language.ring.BoundedFormula (Fin 1) 5 :=
  let x := Term.var (Sum.inl 0)
  let u := Term.var (Sum.inr 0)
  let v := Term.var (Sum.inr 1)
  let w := Term.var (Sum.inr 2)
  let s := Term.var (Sum.inr 3)
  let t := Term.var (Sum.inr 4)
  (x * (u * u + -(numeral 2 * (v * v)) + -1)).bdEqual 0 ⊓
    (x * (v + -(x * w))).bdEqual 0 ⊓ (x * (v * s + -certificate t)).bdEqual 0

/-- Parameter-free native first-order syntax for Xi. -/
def integerGuard : Language.ring.Formula (Fin 1) := integerSystem.exs

@[simp] theorem realize_integerSystem (x : Fin 1 → R) (w : Fin 5 → R) :
    integerSystem.Realize x w ↔ DiophantineConstants.System (x 0) (w 0) (w 1) (w 2) (w 3) (w 4) := by
  simp [integerSystem, DiophantineConstants.System, pow_two, sub_eq_add_neg, and_assoc]

/-- The native formula has exactly the already-proved literal existential predicate as semantics. -/
theorem realize_integerGuard (x : Fin 1 → R) :
    integerGuard.Realize x ↔ DiophantineConstants.Xi (x 0) := by
  rw [integerGuard, BoundedFormula.realize_exs]
  simp only [realize_integerSystem]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w 0, w 1, w 2, w 3, w 4, hw⟩
  · rintro ⟨u, v, w, s, t, h⟩
    exact ⟨![u, v, w, s, t], h⟩

/-- Four square witnesses in the ambient ring; they are not required to be standard. -/
def fourSquares : Language.ring.Formula (Fin 1) :=
  let s : Fin 4 → Language.ring.Term (Fin 1 ⊕ Fin 4) := fun j => Term.var (Sum.inr j)
  ((Term.var (Sum.inl 0)).bdEqual
    ((s 0 * s 0 + s 1 * s 1) + s 2 * s 2 + s 3 * s 3)).exs

/-- Parameter-free native first-order syntax for the natural-number guard. -/
def naturalGuard : Language.ring.Formula (Fin 1) := integerGuard ⊓ fourSquares

theorem realize_fourSquares (x : Fin 1 → R) :
    fourSquares.Realize x ↔ ∃ s : Fin 4 → R, x 0 = ∑ j, s j ^ 2 := by
  simp [fourSquares, BoundedFormula.realize_exs, Fin.sum_univ_succ, pow_two, add_assoc]

theorem realize_naturalGuard (x : Fin 1 → R) :
    naturalGuard.Realize x ↔ DiophantineConstants.Xi (x 0) ∧
      ∃ s : Fin 4 → R, x 0 = ∑ j, s j ^ 2 := by
  simp only [naturalGuard, Formula.realize_inf, realize_integerGuard, realize_fourSquares]

/-- Any ring in which Xi defines the integer constants has a native parameter-free definition. -/
theorem integerConstants_definable
    (hXi : ∀ x : R, DiophantineConstants.Xi x ↔ ∃ a : ℤ, x = (a : R)) :
    (∅ : Set R).Definable₁ Language.ring (Set.range (Int.cast : ℤ → R)) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨integerGuard, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, realize_integerGuard, hXi, Set.mem_range]
  exact exists_congr fun _ => eq_comm

/-- In the ordered case, the same guard also defines the ordinary natural numbers. -/
theorem naturalConstants_definable [LinearOrder R] [IsStrictOrderedRing R]
    (hXi : ∀ x : R, DiophantineConstants.Xi x ↔ ∃ a : ℤ, x = (a : R)) :
    (∅ : Set R).Definable₁ Language.ring (Set.range (Nat.cast : ℕ → R)) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨naturalGuard, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, realize_naturalGuard, Set.mem_range]
  rw [← NaturalNumbersDefinition.natural_iff_standard_four_squares _ hXi]
  exact exists_congr fun _ => eq_comm

end Surreal.ArithmeticGuards
