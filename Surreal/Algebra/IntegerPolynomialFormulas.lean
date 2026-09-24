import Surreal.Algebra.ArithmeticGuards
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Parameter-free integer polynomial formulas

Explicit ring-language syntax for the inequalities in `odg:def:thm:saturation`.
The constructors use signed integer numerals, addition and multiplication.
Their semantics agree with Mathlib's polynomial evaluation in any commutative ring.
-/

namespace Surreal.IntegerPolynomialFormulas
open FirstOrder FirstOrder.Language

/-- Signed integer numerals in the pure ring language. -/
def integerNumeral {α : Type*} : ℤ → Language.ring.Term α
  | .ofNat n => ArithmeticGuards.numeral n
  | .negSucc n => -ArithmeticGuards.numeral (n + 1)

/-- Natural powers, expanded using multiplication. -/
def power {α : Type*} (t : Language.ring.Term α) : ℕ → Language.ring.Term α
  | 0 => 1
  | n + 1 => power t n * t

/-- The first `n` coefficients, with their powers of the distinguished variable. -/
def partialSum {α : Type*} (a : ℕ → ℤ) (t : Language.ring.Term α) :
    ℕ → Language.ring.Term α
  | 0 => 0
  | n + 1 => partialSum a t n + integerNumeral (a n) * power t n

/-- A finite explicit term for an integer polynomial. -/
noncomputable def polynomialTerm {α : Type*} (p : Polynomial ℤ) (t : Language.ring.Term α) :
    Language.ring.Term α := partialSum p.coeff t (p.natDegree + 1)

/-- The parameter-free inequality `p(x) ≠ 0`, with a single free variable. -/
noncomputable def nonvanishing (p : Polynomial ℤ) : Language.ring.Formula (Fin 1) :=
  ((polynomialTerm p (Term.var 0)).equal 0).not

variable {R : Type*} [CommRing R] [FirstOrder.Ring.CompatibleRing R]

@[simp] theorem realize_integerNumeral {α : Type*} (z : ℤ) (v : α → R) :
    (integerNumeral z).realize v = (z : R) := by
  cases z <;> simp [integerNumeral, Int.cast_negSucc]

@[simp] theorem realize_power {α : Type*} (t : Language.ring.Term α) (n : ℕ) (v : α → R) :
    (power t n).realize v = t.realize v ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ]

@[simp] theorem realize_partialSum {α : Type*} (a : ℕ → ℤ) (t : Language.ring.Term α)
    (n : ℕ) (v : α → R) :
    (partialSum a t n).realize v = ∑ i ∈ Finset.range n, (a i : R) * t.realize v ^ i := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => simp [partialSum, ih, Finset.sum_range_succ]

@[simp] theorem realize_polynomialTerm {α : Type*} (p : Polynomial ℤ)
    (t : Language.ring.Term α) (v : α → R) :
    (polynomialTerm p t).realize v = p.eval₂ (Int.castRingHom R) (t.realize v) := by
  simp [polynomialTerm, Polynomial.eval₂_eq_sum_range]

/-- The native inequality has exactly the intended polynomial semantics. -/
@[simp] theorem realize_nonvanishing (p : Polynomial ℤ) (v : Fin 1 → R) :
    (nonvanishing p).Realize v ↔ p.eval₂ (Int.castRingHom R) (v 0) ≠ 0 := by
  simp [nonvanishing]

end Surreal.IntegerPolynomialFormulas
