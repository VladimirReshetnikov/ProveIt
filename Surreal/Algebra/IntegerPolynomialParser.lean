import Surreal.Algebra.RingFormulaEquality
import Surreal.Algebra.IntegerPolynomialCode
import Surreal.Algebra.AlgebraicOmittedType

/-!
# An executable recognizer for the explicit omitted type

The syntactic decision procedure in `odg:def:thm:saturation`. A structural
parser proposes a finite coefficient list, then checks that it is canonical
and regenerates exactly the input native formula. Its correctness concerns
syntactic membership, not merely logical equivalence of formulas.
-/

namespace Surreal.IntegerPolynomialParser
open FirstOrder FirstOrder.Language
open IntegerPolynomialFormulas IntegerPolynomialCode

/-- Evaluate a ring term over the integers, sending all variables to zero.
This computational evaluator is used only to propose coefficient numerals. -/
def integerValue {α : Type*} : Language.ring.Term α → ℤ
  | .var _ => 0
  | .func .zero _ => 0
  | .func .one _ => 1
  | .func .add ts => integerValue (ts 0) + integerValue (ts 1)
  | .func .mul ts => integerValue (ts 0) * integerValue (ts 1)
  | .func .neg ts => -integerValue (ts 0)

@[simp] theorem integerValue_add {α : Type*} (s t : Language.ring.Term α) :
    integerValue (s + t) = integerValue s + integerValue t := rfl

@[simp] theorem integerValue_neg {α : Type*} (t : Language.ring.Term α) :
    integerValue (-t) = -integerValue t := rfl

@[simp] theorem integerValue_one {α : Type*} :
    integerValue (1 : Language.ring.Term α) = 1 := rfl

/-- Read the coefficient position of a proposed monomial term. -/
def monomialCoefficient {α : Type*} : Language.ring.Term α → ℤ
  | .func .mul ts => integerValue (ts 0)
  | _ => 0

/-- Read a proposed finite sum, retaining zeros between nonzero coefficients. -/
def readCoefficients {α : Type*} : Language.ring.Term α → List ℤ
  | .func .add ts => readCoefficients (ts 0) ++ [monomialCoefficient (ts 1)]
  | _ => []

@[simp] theorem monomialCoefficient_mul {α : Type*} (s t : Language.ring.Term α) :
    monomialCoefficient (s * t) = integerValue s := rfl

@[simp] theorem readCoefficients_add {α : Type*} (s t : Language.ring.Term α) :
    readCoefficients (s + t) = readCoefficients s ++ [monomialCoefficient t] := rfl

@[simp] theorem integerValue_numeral {α : Type*} (n : ℕ) :
    integerValue (ArithmeticGuards.numeral (α := α) n) = (n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ArithmeticGuards.numeral, ih, Nat.cast_add, Nat.cast_one]

@[simp] theorem integerValue_integerNumeral {α : Type*} (z : ℤ) :
    integerValue (integerNumeral (α := α) z) = z := by
  cases z <;> simp [integerNumeral, Int.negSucc_eq]

/-- The parser recovers every coefficient of a generated finite sum. -/
theorem readCoefficients_partialSum {α : Type*} (a : ℕ → ℤ)
    (t : Language.ring.Term α) (n : ℕ) :
    readCoefficients (partialSum a t n) = List.ofFn (fun i : Fin n => a i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [partialSum, readCoefficients_add, monomialCoefficient_mul, integerValue_integerNumeral, ih,
      List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

@[simp] theorem integerValue_relabel {α β : Type*} (f : α → β) (t : Language.ring.Term α) :
    integerValue (t.relabel f) = integerValue t := by
  induction t with
  | var a => rfl
  | func g ts ih => cases g <;> simp [Term.relabel, integerValue, ih]

@[simp] theorem monomialCoefficient_relabel {α β : Type*} (f : α → β)
    (t : Language.ring.Term α) : monomialCoefficient (t.relabel f) = monomialCoefficient t := by
  cases t with
  | var a => rfl
  | func g ts => cases g <;> simp [Term.relabel, monomialCoefficient]

@[simp] theorem readCoefficients_relabel {α β : Type*} (f : α → β)
    (t : Language.ring.Term α) : readCoefficients (t.relabel f) = readCoefficients t := by
  induction t with
  | var a => rfl
  | func g ts ih => cases g <;> simp [Term.relabel, readCoefficients, ih]

/-- A parameter-free inequality constructed directly from a finite list. -/
def inequality (l : List ℤ) : Language.ring.Formula (Fin 1) :=
  ((term l (Term.var 0)).equal 0).not

/-- Extract a proposed coefficient list from the left term of a negated equation. -/
def candidate : Language.ring.Formula (Fin 1) → List ℤ
  | .imp (.equal lhs _) .falsum => readCoefficients lhs
  | _ => []

local instance {n : ℕ} : DecidableEq (Language.ring.BoundedFormula (Fin 1) n) :=
  RingFormulaEquality.decidableEq

/-- Check the canonical coefficient condition and exact syntactic regeneration. -/
def checkNonvanishing (φ : Language.ring.Formula (Fin 1)) : Bool :=
  decide (Canonical (candidate φ) ∧ φ = inequality (candidate φ))

/-- Check membership in the guard plus all nonzero polynomial inequalities. -/
def checkType (δ φ : Language.ring.Formula (Fin 1)) : Bool :=
  decide (φ = δ) || checkNonvanishing φ

@[simp] theorem inequality_coefficients (p : Polynomial ℤ) :
    inequality (coefficients p) = nonvanishing p := by
  simp [inequality, nonvanishing, term_coefficients]

/-- A canonical code produces exactly its decoded polynomial inequality. -/
theorem inequality_eq_nonvanishing {l : List ℤ} (hl : Canonical l) :
    inequality l = nonvanishing (toPolynomial l) := by
  rw [← inequality_coefficients, coefficients_toPolynomial hl]

/-- The candidate parser is complete on every canonical polynomial inequality. -/
@[simp] theorem candidate_nonvanishing (p : Polynomial ℤ) :
    candidate (nonvanishing p) = coefficients p := by
  change readCoefficients ((polynomialTerm p (Term.var (0 : Fin 1))).relabel Sum.inl) = coefficients p
  rw [readCoefficients_relabel]
  exact readCoefficients_partialSum p.coeff _ _

/-- The executable check recognizes exactly the nonzero integer polynomial inequalities. -/
theorem checkNonvanishing_iff (φ : Language.ring.Formula (Fin 1)) :
    checkNonvanishing φ = true ↔ ∃ p : Polynomial ℤ, p ≠ 0 ∧ φ = nonvanishing p := by
  simp only [checkNonvanishing, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, he⟩
    exact ⟨toPolynomial (candidate φ), toPolynomial_ne_zero hc,
      he.trans (inequality_eq_nonvanishing hc)⟩
  · rintro ⟨p, hp, rfl⟩
    simpa using (canonical_coefficients_iff p).mpr hp

/-- Executable membership in the actual native formula set used by the omitted-type proof. -/
theorem checkType_iff (δ φ : Language.ring.Formula (Fin 1)) :
    checkType δ φ = true ↔ φ ∈ AlgebraicOmittedType.formulas δ := by
  simp only [checkType, Bool.or_eq_true, decide_eq_true_eq, checkNonvanishing_iff,
    AlgebraicOmittedType.formulas, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq]
  exact or_congr Iff.rfl (exists_congr fun _ => and_congr_right fun _ => eq_comm)

/-- Constructive decidability of membership, obtained from the verified executable recognizer. -/
abbrev membershipDecidable (δ : Language.ring.Formula (Fin 1)) :
    DecidablePred (fun φ => φ ∈ AlgebraicOmittedType.formulas δ) := fun φ =>
  decidable_of_iff (checkType δ φ = true) (checkType_iff δ φ)

end Surreal.IntegerPolynomialParser
