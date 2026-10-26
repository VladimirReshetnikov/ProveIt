import DiophantineConsistency.Representation
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Executable coefficient extraction from stored arithmetic syntax

Expand syntax to a finite list of monomials, retaining duplicate terms.
The list is executable data: exponent vectors are functions on `Fin n`.
Only its interpretation as Mathlib's ordinary polynomial is noncomputable.
-/

namespace DiophantineConsistency.SyntaxCoefficients

abbrev Term (n : ℕ) := (Fin n → ℕ) × ℤ

/-- Negate coefficients without changing exponent vectors. -/
def negate {n : ℕ} (terms : List (Term n)) : List (Term n) :=
  terms.map fun t => (t.1, -t.2)

/-- Distribute a product, leaving collection of like terms to the reader. -/
def multiply {n : ℕ} (left right : List (Term n)) : List (Term n) :=
  left.flatMap fun a => right.map fun b => (a.1 + b.1, a.2 * b.2)

/-- A sparse expansion specified by structural recursion on arithmetic syntax. -/
def expand {n : ℕ} : Expr (Fin n) → List (Term n)
  | .constant a => [(0, a)]
  | .var i => [(fun j => if j = i then 1 else 0, 1)]
  | .add p q => expand p ++ expand q
  | .sub p q => expand p ++ negate (expand q)
  | .mul p q => multiply (expand p) (expand q)

/-- Sum all coefficients with the requested exponent vector. -/
def coefficient {n : ℕ} (terms : List (Term n)) (d : Fin n → ℕ) : ℤ :=
  (terms.map fun t => if t.1 = d then t.2 else 0).sum

/-- The ordinary finite-support exponent vector, used only for theorems. -/
noncomputable def exponent {n : ℕ} (d : Fin n → ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm d

@[simp] theorem exponent_apply {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    exponent d i = d i := by simp [exponent]

@[simp] theorem exponent_zero {n : ℕ} : exponent (0 : Fin n → ℕ) = 0 := by
  ext i; simp

@[simp] theorem exponent_add {n : ℕ} (a b : Fin n → ℕ) :
    exponent (a + b) = exponent a + exponent b := by
  ext i; simp

@[simp] theorem exponent_inj {n : ℕ} (a b : Fin n → ℕ) :
    exponent a = exponent b ↔ a = b :=
  Finsupp.equivFunOnFinite.symm.injective.eq_iff

/-- The ordinary polynomial denoted by the expanded list. -/
noncomputable def interpret {n : ℕ} : List (Term n) → MvPolynomial (Fin n) ℤ
  | [] => 0
  | t :: ts => MvPolynomial.monomial (exponent t.1) t.2 + interpret ts

private theorem interpret_eq_sum {n : ℕ} (terms : List (Term n)) :
    interpret terms = (terms.map fun t => MvPolynomial.monomial (exponent t.1) t.2).sum := by
  induction terms with
  | nil => rfl
  | cons a as ih => simp only [interpret, List.map_cons, List.sum_cons, ih]

@[simp] theorem interpret_append {n : ℕ} (left right : List (Term n)) :
    interpret (left ++ right) = interpret left + interpret right := by
  simp only [interpret_eq_sum, List.map_append, List.sum_append]

@[simp] theorem interpret_negate {n : ℕ} (terms : List (Term n)) :
    interpret (negate terms) = -interpret terms := by
  simp only [interpret_eq_sum, negate, List.map_map, Function.comp_def, map_neg]
  simpa only [List.map_map, Function.comp_def] using
    (List.sum_neg (terms.map fun t =>
      (MvPolynomial.monomial (exponent t.1) t.2 : MvPolynomial (Fin n) ℤ))).symm

@[simp] theorem interpret_multiply {n : ℕ} (left right : List (Term n)) :
    interpret (multiply left right) = interpret left * interpret right := by
  simp only [interpret_eq_sum, multiply, List.flatMap_def, List.map_flatten,
    List.sum_flatten, List.map_map, Function.comp_def, exponent_add,
    ← MvPolynomial.monomial_mul, List.sum_map_mul_left, List.sum_map_mul_right]

/-- Sparse expansion denotes exactly the polynomial of the supplied syntax. -/
theorem interpret_expand {n : ℕ} (e : Expr (Fin n)) :
    interpret (expand e) = e.toPolynomial := by
  induction e with
  | constant a => simp [expand, interpret, Expr.toPolynomial, MvPolynomial.monomial_zero']
  | var i =>
    have hs : exponent (fun j : Fin n => if j = i then 1 else 0) = Finsupp.single i 1 := by
      ext j; simp [Finsupp.single_apply, eq_comm]
    simp [expand, interpret, Expr.toPolynomial, hs, MvPolynomial.X]
  | add p q hp hq => simp [expand, Expr.toPolynomial, hp, hq]
  | sub p q hp hq => simp [expand, Expr.toPolynomial, hp, hq, sub_eq_add_neg]
  | mul p q hp hq => simp [expand, Expr.toPolynomial, hp, hq]

/-- The executable list reader agrees with the standard coefficient map. -/
theorem coefficient_interpret {n : ℕ} (terms : List (Term n)) (d : Fin n → ℕ) :
    coefficient terms d = MvPolynomial.coeff (exponent d) (interpret terms) := by
  rw [interpret_eq_sum]
  change _ = (MvPolynomial.coeffAddMonoidHom (exponent d)) _
  simp only [map_list_sum, List.map_map, Function.comp_def,
    MvPolynomial.coeffAddMonoidHom_apply, MvPolynomial.coeff_monomial, exponent_inj, coefficient]

theorem coefficient_expand {n : ℕ} (e : Expr (Fin n)) (d : Fin n → ℕ) :
    coefficient (expand e) d = MvPolynomial.coeff (exponent d) e.toPolynomial := by
  rw [coefficient_interpret, interpret_expand]

#print axioms coefficient_expand

end DiophantineConsistency.SyntaxCoefficients
