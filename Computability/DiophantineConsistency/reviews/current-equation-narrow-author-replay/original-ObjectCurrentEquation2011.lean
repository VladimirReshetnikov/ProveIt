import DiophantineConsistency.CurrentPolynomialWindow2011
import DiophantineConsistency.ObjectNaturalDiscrete
import DiophantineConsistency.WeightedExpressionDegree

/-!
# Literal current equation syntax and its object-language positive domain

The expression below is the entire Carrier65 front with the current four
ports, including the one source-high-mask shift. Positive integer variables
are represented by fourteen unrestricted natural variables plus one.

The sentence semantics quantifies over every internal natural in any model
of the supplied set-theoretic axioms. No standardness, consistency, machine
semantics, or internal consistency-equivalence premise is used or concluded.
The large constants and the split-natural compilation are not expanded.
-/

set_option Elab.async false

noncomputable section
namespace DiophantineConsistency.ObjectCurrentEquation2011

/-- Literal arithmetic syntax, in the same coordinate and port order as
`Carrier65.core`. All four ports are single integer-constant leaves. -/
def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let n : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let y : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let S := i * delta * c ^ 2
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let U := S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  let Z := delta * f ^ 2 - S ^ 2
  P * Q * U * W * Z - delta

theorem evalRing_expressionAt {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt p).evalRing v = Carrier65.value (fun j => (p j : R)) v := by
  simp only [expressionAt, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    Carrier65.value, Carrier65.core]

theorem eval_expressionAt (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    (expressionAt p).eval v = Carrier65.value p v := by
  simp only [expressionAt, Expr.eval_add, Expr.eval_sub, Expr.eval_mul,
    Expr.eval_pow, Expr.eval_var, Expr.eval_constant, Carrier65.value, Carrier65.core]
  rfl

/-- The syntax is the actual polynomial, not only a zero-set equivalent one. -/
theorem polynomial_expressionAt (p : Fin 4 → ℤ) :
    (expressionAt p).toPolynomial = Carrier65.polynomial p := by
  rw [← Expr.evalRing_X, evalRing_expressionAt]
  rfl

/-- The current ports retain the full kernel and both complete masks. -/
def expression : Expr (Fin 14) := expressionAt CurrentWindowCarry2011.ports

theorem polynomial_expression :
    expression.toPolynomial = CurrentPolynomialWindow2011.polynomial :=
  polynomial_expressionAt CurrentWindowCarry2011.ports

theorem eval_expression (v : Fin 14 → ℤ) :
    expression.eval v = MvPolynomial.eval v CurrentPolynomialWindow2011.polynomial := by
  rw [← polynomial_expression, Expr.eval_toPolynomial]

/-- This substitution changes the domain, without adding any variables. -/
def positiveShift {σ : Type*} (e : Expr σ) : Expr σ :=
  e.subst (fun i => Expr.var i + Expr.constant 1)

theorem eval_positiveShift {σ : Type*} (e : Expr σ) (v : σ → ℤ) :
    (positiveShift e).eval v = e.eval (fun i => v i + 1) := by
  simp only [positiveShift, Expr.eval_subst, Expr.eval_add, Expr.eval_var,
    Expr.eval_constant]

def naturalExpression : Expr (Fin 14) := positiveShift expression

theorem eval_naturalExpression (v : Fin 14 → ℕ) :
    naturalExpression.eval (fun i => (v i : ℤ)) =
      MvPolynomial.eval (fun i => (v i : ℤ) + 1)
        CurrentPolynomialWindow2011.polynomial := by
  exact (eval_positiveShift expression _).trans (eval_expression _)

/-- Exact external positive-integral domain correspondence. -/
theorem natural_zero_iff_positive_zero :
    (∃ v : Fin 14 → ℕ, naturalExpression.eval (fun i => (v i : ℤ)) = 0) ↔
      CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (v i : ℤ) + 1, ?_, ?_⟩
    · intro i
      change 0 < (v i : ℤ) + 1
      have := Int.natCast_nonneg (v i)
      omega
    · exact (eval_naturalExpression v).symm.trans hv
  · rintro ⟨v, hv, hz⟩
    let x : Fin 14 → ℕ := fun i => (v i - 1).toNat
    have hx : (fun i => (x i : ℤ) + 1) = v := by
      funext i
      have hi : 0 ≤ v i - 1 := by have := hv i; omega
      simp only [x, Int.toNat_of_nonneg hi]
      omega
    refine ⟨x, ?_⟩
    rw [eval_naturalExpression, hx]
    exact hz

/-- The generic pair identity prevents any expansion of the large current
split-natural tree. It holds over every commutative semiring. -/
theorem split_positiveShift {σ R : Type*} [CommSemiring R]
    (e : Expr σ) (v : σ → R) :
    ((positiveShift e).splitNatural.1.evalSemiring v,
      (positiveShift e).splitNatural.2.evalSemiring v) =
      (e.splitNatural.1.evalSemiring (fun i => v i + 1),
       e.splitNatural.2.evalSemiring (fun i => v i + 1)) := by
  induction e <;>
    simp_all [positiveShift, Expr.subst, Expr.splitNatural, NatExpr.evalSemiring]

def InternalZero {σ R : Type*} [CommSemiring R] (e : Expr σ) (v : σ → R) : Prop :=
  e.splitNatural.1.evalSemiring v = e.splitNatural.2.evalSemiring v

theorem internalZero_positiveShift {σ R : Type*} [CommSemiring R]
    (e : Expr σ) (v : σ → R) :
    InternalZero (positiveShift e) v ↔ InternalZero e (fun i => v i + 1) :=
  Iff.of_eq (congrArg (fun p : R × R => p.1 = p.2) (split_positiveShift e v))

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- Every positive internal natural has an internal predecessor. The tuple
is not restricted to external numeral values. -/
theorem internal_positive_iff_successor (H : ZFAxioms mem) (y : Natural H) :
    0 < y ↔ ∃ x : Natural H, y = x + 1 := by
  simpa only [zero_add] using ObjectNaturalDiscrete.lt_iff_exists_add_one H 0 y

theorem no_shifted_zero_iff_positive (H : ZFAxioms mem) {n : ℕ}
    (e : Expr (Fin n)) :
    (∀ v : Fin n → Natural H, ¬ InternalZero (positiveShift e) v) ↔
      ∀ v : Fin n → Natural H, (∀ i, 0 < v i) → ¬ InternalZero e v := by
  classical
  constructor
  · intro h v hv
    have hs : ∀ i, ∃ x : Natural H, v i = x + 1 :=
      fun i => (internal_positive_iff_successor H (v i)).mp (hv i)
    choose x hx using hs
    have he : v = fun i => x i + 1 := funext hx
    rw [he]
    exact fun hz => h x ((internalZero_positiveShift e x).mpr hz)
  · intro h v hz
    apply h (fun i => v i + 1)
    · intro i
      exact (internal_positive_iff_successor H _).mpr ⟨v i, rfl⟩
    · exact (internalZero_positiveShift e v).mp hz

/-- The supplied closed first-order set-theory sentence. -/
def unsolvabilitySentence : Form := ObjectPolynomial.noZeroForm naturalExpression

theorem sentence_unsolvabilitySentence : Sentence unsolvabilitySentence :=
  ObjectPolynomial.sentence_noZeroForm naturalExpression

/-- Exact all-model semantics for the literal current positive-domain equation.
This theorem is not an internal consistency-equivalence theorem. -/
theorem sat_unsolvabilitySentence_iff (H : ZFAxioms mem) :
    (∀ ee : ℕ → V, Sat mem ee unsolvabilitySentence) ↔
      ∀ v : Fin 14 → Natural H, (∀ i, 0 < v i) → ¬ InternalZero expression v := by
  exact (ObjectNaturalSemiring.sat_noZeroForm_iff H naturalExpression).trans
    (no_shifted_zero_iff_positive H expression)

/-- Standard numerals give the exact current positive polynomial evaluation. -/
theorem equationRel_numerals_iff (H : ZFAxioms mem) (v : Fin 14 → ℕ) :
    ObjectPolynomial.EquationRel H naturalExpression (fun i => natV H (v i)) ↔
      MvPolynomial.eval (fun i => (v i : ℤ) + 1)
        CurrentPolynomialWindow2011.polynomial = 0 := by
  rw [ObjectPolynomial.equationRel_numerals_iff, eval_naturalExpression]

attribute [local irreducible] expression naturalExpression

/-- Satisfaction rules out external positive zeros; no converse from only
standard tuples is asserted for a nonstandard model. -/
theorem no_positive_zero_of_sat (H : ZFAxioms mem)
    (h : ∀ ee : ℕ → V, Sat mem ee unsolvabilitySentence) :
    ¬ CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial := by
  intro hz
  exact ObjectPolynomial.no_external_zero_of_sat H naturalExpression h
    (natural_zero_iff_positive_zero.mpr hz)

end DiophantineConsistency.ObjectCurrentEquation2011
