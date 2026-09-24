import Surreal.Algebra.IntegerPolynomialFormulas
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Canonical finite coefficient codes for nonzero integer polynomials

The coefficient-code prerequisite for computability in `odg:def:thm:saturation`.
A canonical code is a nonempty list of signed integers, in increasing degree,
with nonzero final entry. The correspondence with nonzero Mathlib polynomials
preserves the explicit native ring terms constructed earlier.
-/

namespace Surreal.IntegerPolynomialCode
open FirstOrder FirstOrder.Language
open IntegerPolynomialFormulas

/-- Missing coefficients of a finite list are zero. -/
def coefficient (l : List ℤ) (n : ℕ) : ℤ := l[n]?.getD 0

/-- Canonical nonzero coefficient lists have no trailing zero. -/
def Canonical (l : List ℤ) : Prop := 0 < l.length ∧ coefficient l (l.length - 1) ≠ 0

instance (l : List ℤ) : Decidable (Canonical l) := inferInstanceAs
  (Decidable (0 < l.length ∧ coefficient l (l.length - 1) ≠ 0))

/-- A list determines a Mathlib polynomial by its finite coefficient vector. -/
noncomputable def toPolynomial (l : List ℤ) : Polynomial ℤ :=
  Polynomial.ofFn l.length (fun i => l[i.val])

/-- Every polynomial has its coefficient list through its natural degree. -/
noncomputable def coefficients (p : Polynomial ℤ) : List ℤ :=
  List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i.val)

@[simp] theorem coefficient_toPolynomial (l : List ℤ) (n : ℕ) :
    (toPolynomial l).coeff n = coefficient l n := by
  by_cases hn : n < l.length
  · simp [toPolynomial, coefficient, hn]
  · simp [toPolynomial, coefficient, hn, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hn)]

@[simp] theorem length_coefficients (p : Polynomial ℤ) :
    (coefficients p).length = p.natDegree + 1 := by simp [coefficients]

@[simp] theorem coefficient_coefficients (p : Polynomial ℤ) (n : ℕ) :
    coefficient (coefficients p) n = p.coeff n := by
  by_cases hn : n < p.natDegree + 1
  · simp only [coefficient, coefficients, List.getElem?_ofFn, dif_pos hn, Option.getD_some]
  · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega : p.natDegree < n)
    simp [coefficient, coefficients, hn, hz]

/-- Coefficient decoding recovers the original polynomial. -/
@[simp] theorem toPolynomial_coefficients (p : Polynomial ℤ) :
    toPolynomial (coefficients p) = p := by ext n; simp

/-- Precisely the nonzero polynomials have canonical coefficient lists. -/
theorem canonical_coefficients_iff (p : Polynomial ℤ) : Canonical (coefficients p) ↔ p ≠ 0 := by
  simp [Canonical, Polynomial.coeff_natDegree]

/-- A canonical list decodes to a nonzero polynomial. -/
theorem toPolynomial_ne_zero {l : List ℤ} (hl : Canonical l) : toPolynomial l ≠ 0 := by
  intro h
  apply hl.2
  rw [← coefficient_toPolynomial, h, Polynomial.coeff_zero]

/-- Canonical list length is exactly one more than the decoded polynomial's degree. -/
theorem natDegree_add_one {l : List ℤ} (hl : Canonical l) :
    (toPolynomial l).natDegree + 1 = l.length := by
  have hlt := Polynomial.ofFn_natDegree_lt hl.1 (fun i : Fin l.length => l[i.val])
  have hle := Polynomial.le_natDegree_of_ne_zero (p := toPolynomial l)
    (n := l.length - 1) (by simpa using hl.2)
  change (toPolynomial l).natDegree < l.length at hlt
  omega

/-- Encoding a decoded canonical list recovers the list, so the syntax is unique. -/
theorem coefficients_toPolynomial {l : List ℤ} (hl : Canonical l) :
    coefficients (toPolynomial l) = l := by
  apply List.ext_getElem
  · simpa using natDegree_add_one hl
  · intro i hi hj
    have h := coefficient_toPolynomial l i
    change (List.ofFn (fun j : Fin ((toPolynomial l).natDegree + 1) =>
      (toPolynomial l).coeff j.val))[i] = l[i]
    rw [List.getElem_ofFn]
    simpa only [coefficient, List.getElem?_eq_getElem hj, Option.getD_some] using h

/-- A computational term constructor directly on finite signed coefficient lists. -/
def term {α : Type*} (l : List ℤ) (t : Language.ring.Term α) : Language.ring.Term α :=
  partialSum (coefficient l) t l.length

/-- The finite code constructs exactly the earlier native polynomial term. -/
theorem term_coefficients {α : Type*} (p : Polynomial ℤ) (t : Language.ring.Term α) :
    term (coefficients p) t = polynomialTerm p t := by
  have h : coefficient (coefficients p) = p.coeff := funext (coefficient_coefficients p)
  simp only [term, polynomialTerm, length_coefficients, h]

/-- Canonical list syntax agrees with its decoded polynomial's canonical syntax. -/
theorem term_eq_polynomialTerm {α : Type*} {l : List ℤ} (hl : Canonical l)
    (t : Language.ring.Term α) : term l t = polynomialTerm (toPolynomial l) t := by
  rw [← term_coefficients, coefficients_toPolynomial hl]

end Surreal.IntegerPolynomialCode
