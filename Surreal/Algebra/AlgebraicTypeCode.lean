import Surreal.Algebra.IntegerPolynomialSyntaxRelabel
import Surreal.Algebra.IntegerPolynomialParserComputability
import Surreal.Algebra.RingFormulaFixedContext

/-!
# Exact recognition of the algebraic omitted type on formula codes

The code-space recognizer for `odg:def:thm:saturation`. It proposes a finite
coefficient list from the second token, then checks exact regeneration of the
whole canonical formula. Incorrect surrounding syntax cannot be accepted.
-/

namespace Surreal.AlgebraicTypeCode
open FirstOrder FirstOrder.Language
open IntegerPolynomialFormulas IntegerPolynomialCode IntegerPolynomialParser

local instance : DecidableEq RingFormulaCode.Token := inferInstance

/-- Read the proposed left-term code from an equation token, or return an empty proposal. -/
def leftTermCode : RingFormulaCode.Token → List RingTermCode.Token
  | .inl a => a.2.1
  | _ => []

/-- Propose coefficients by inspecting one term code; exact surrounding syntax is checked later. -/
def candidate (l : List RingFormulaCode.Token) : List ℤ :=
  ((RingTermCode.decode (leftTermCode (l.getD 1 (.inr (.inl 0))))).map
    (readCoefficients (α := ℕ))).getD []

/-- The canonical code of a parameter-free polynomial inequality. -/
def inequality (l : List ℤ) : List RingFormulaCode.Token :=
  [.inr (.inr 0), .inl (0, RingTermCode.encode (term l (Term.var 0)), [.inr 0]), .inr (.inl 0)]

/-- The direct code constructor agrees with encoding the existing native inequality. -/
theorem inequality_encode (l : List ℤ) :
    RingFormulaCode.encode (IntegerPolynomialParser.inequality l) = inequality l := by
  simp [IntegerPolynomialParser.inequality, Formula.not, BoundedFormula.not, Term.equal, Term.bdEqual,
    RingFormulaCode.encode, RingFormulaCode.termEquiv, Term.relabelEquiv_apply,
    RingTermScope.encode, RingTermScope.widen, inequality]

/-- The coefficient proposal is complete on every list-generated inequality code. -/
@[simp] theorem candidate_inequality (l : List ℤ) : candidate (inequality l) = l := by
  simp [candidate, inequality, leftTermCode, readCoefficients_codeTerm]

/-- Check canonicity and exact regeneration of the entire inequality code. -/
def checkNonvanishing (l : List RingFormulaCode.Token) : Bool :=
  decide (IntegerPolynomialCode.Canonical (candidate l) ∧ l = inequality (candidate l))

/-- The code checker accepts precisely the serialized inequalities for nonzero integer polynomials. -/
theorem checkNonvanishing_iff (l : List RingFormulaCode.Token) :
    checkNonvanishing l = true ↔ ∃ p : Polynomial ℤ, p ≠ 0 ∧
      l = RingFormulaCode.encode (nonvanishing p) := by
  simp only [checkNonvanishing, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, he⟩
    refine ⟨toPolynomial (candidate l), toPolynomial_ne_zero hc, ?_⟩
    rw [← IntegerPolynomialParser.inequality_eq_nonvanishing hc, inequality_encode]
    exact he
  · rintro ⟨p, hp, rfl⟩
    rw [← IntegerPolynomialParser.inequality_coefficients, inequality_encode, candidate_inequality]
    exact ⟨(canonical_coefficients_iff p).mpr hp, rfl⟩

/-- Membership in the guard-plus-polynomial type, on the full finite code space. -/
def checkType (δ : Language.ring.Formula (Fin 1)) (l : List RingFormulaCode.Token) : Bool :=
  decide (l = RingFormulaCode.encode δ) || checkNonvanishing l

/-- The encoded recognizer agrees exactly with membership in the original native formula set. -/
theorem checkType_encode_iff (δ φ : Language.ring.Formula (Fin 1)) :
    checkType δ (RingFormulaCode.encode φ) = true ↔ φ ∈ AlgebraicOmittedType.formulas δ := by
  have hi : Function.Injective (RingFormulaCode.encode (n := 0)) := by
    intro a b h
    have he := RingFormulaCode.encode_injective (a₁ := ⟨0, a⟩) (a₂ := ⟨0, b⟩) h
    simpa using he
  simp only [checkType, Bool.or_eq_true, decide_eq_true_eq, checkNonvanishing_iff,
    hi.eq_iff, AlgebraicOmittedType.formulas, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq]
  exact or_congr Iff.rfl (exists_congr fun _ => and_congr_right fun _ => eq_comm)

end Surreal.AlgebraicTypeCode
