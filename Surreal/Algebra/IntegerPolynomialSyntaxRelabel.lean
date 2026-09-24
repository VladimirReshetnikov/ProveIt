import Surreal.Algebra.IntegerPolynomialParser

/-!
# Relabeling the explicit polynomial syntax

The bridge from finite-context native polynomial formulas to natural-indexed
term codes used in `odg:def:thm:saturation`.
-/

namespace Surreal.IntegerPolynomialFormulas
open FirstOrder FirstOrder.Language

@[simp] theorem relabel_zero {α β : Type*} (f : α → β) :
    (0 : Language.ring.Term α).relabel f = 0 := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i
@[simp] theorem relabel_one {α β : Type*} (f : α → β) :
    (1 : Language.ring.Term α).relabel f = 1 := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i
@[simp] theorem relabel_neg {α β : Type*} (f : α → β) (t : Language.ring.Term α) :
    (-t).relabel f = -(t.relabel f) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i
  rfl
@[simp] theorem relabel_add {α β : Type*} (f : α → β) (s t : Language.ring.Term α) :
    (s + t).relabel f = s.relabel f + t.relabel f := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem relabel_mul {α β : Type*} (f : α → β) (s t : Language.ring.Term α) :
    (s * t).relabel f = s.relabel f * t.relabel f := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem relabel_numeral {α β : Type*} (f : α → β) (n : ℕ) :
    (ArithmeticGuards.numeral n).relabel f = ArithmeticGuards.numeral n := by
  induction n with
  | zero => exact relabel_zero f
  | succ n ih => simp [ArithmeticGuards.numeral, ih]

@[simp] theorem relabel_integerNumeral {α β : Type*} (f : α → β) (z : ℤ) :
    (integerNumeral z).relabel f = integerNumeral z := by cases z <;> simp [integerNumeral]

@[simp] theorem relabel_power {α β : Type*} (f : α → β) (t : Language.ring.Term α) (n : ℕ) :
    (power t n).relabel f = power (t.relabel f) n := by
  induction n with
  | zero => exact relabel_one f
  | succ n ih => simp [power, ih]

@[simp] theorem relabel_partialSum {α β : Type*} (f : α → β) (a : ℕ → ℤ)
    (t : Language.ring.Term α) (n : ℕ) :
    (partialSum a t n).relabel f = partialSum a (t.relabel f) n := by
  induction n with
  | zero => exact relabel_zero f
  | succ n ih => simp [partialSum, ih]

@[simp] theorem relabel_codeTerm {α β : Type*} (f : α → β) (l : List ℤ)
    (t : Language.ring.Term α) :
    (IntegerPolynomialCode.term l t).relabel f = IntegerPolynomialCode.term l (t.relabel f) :=
  relabel_partialSum f _ _ _

/-- Parsing any list-generated term recovers the entire list, including trailing zeros. -/
theorem readCoefficients_codeTerm {α : Type*} (l : List ℤ) (t : Language.ring.Term α) :
    IntegerPolynomialParser.readCoefficients (IntegerPolynomialCode.term l t) = l := by
  rw [IntegerPolynomialCode.term, IntegerPolynomialParser.readCoefficients_partialSum]
  simp [IntegerPolynomialCode.coefficient]

end Surreal.IntegerPolynomialFormulas
