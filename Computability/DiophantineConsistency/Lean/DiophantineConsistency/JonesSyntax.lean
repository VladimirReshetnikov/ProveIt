import DiophantineConsistency.NinePolynomial
import DiophantineConsistency.RefinedPair
import DiophantineConsistency.Representation
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Arithmetic syntax for the Jones nine-variable equation

Given the starting quartic, this module specifies the final expression by
finite coefficient evaluation, fixed powers, and the closed two-radicand
relation combiner. No polynomial is chosen from a proof of existence.
The imported starting polynomial operations remain noncomputable; this is
not yet a standalone executable compiler from a program to a quartic.
-/

namespace DiophantineConsistency.JonesSyntax

open NinePolynomial Jones1982

/-- Build syntax for a finite initial segment of a univariate polynomial. -/
def coefficientPrefix {σ : Type*} (coefficient : ℕ → ℤ) (e : Expr σ) : ℕ → Expr σ
  | 0 => .constant 0
  | n + 1 => coefficientPrefix coefficient e n + .constant (coefficient n) * e ^ n

@[simp] theorem eval_coefficientPrefix {σ : Type*} (coefficient : ℕ → ℤ)
    (e : Expr σ) (n : ℕ) (a : σ → ℤ) :
    (coefficientPrefix coefficient e n).eval a =
      ∑ i ∈ Finset.range n, coefficient i * e.eval a ^ i := by
  induction n with
  | zero => simp [coefficientPrefix]
  | succ n ih => simp [coefficientPrefix, ih, Finset.sum_range_succ]

/-- Literal coefficient evaluation, with a finite degree-based bound. -/
noncomputable def univariate {σ : Type*} (p : Polynomial ℤ) (e : Expr σ) : Expr σ :=
  coefficientPrefix (fun i => p.coeff i) e (p.natDegree + 1)

@[simp] theorem eval_univariate {σ : Type*} (p : Polynomial ℤ) (e : Expr σ)
    (a : σ → ℤ) : (univariate p e).eval a = p.eval (e.eval a) := by
  rw [univariate, eval_coefficientPrefix, Polynomial.eval_eq_sum_range]

/-- Evaluate all Jones syntax fields into the existing integer record. -/
def evalExprVars {σ : Type*} (a : σ → ℤ) (v : RingVars (Expr σ)) : Jones1982.Nine.Vars :=
  ⟨v.R.eval a, v.N.eval a, v.b.eval a, v.g.eval a, v.G.eval a,
    v.h.eval a, v.s.eval a, v.w.eval a, v.φ.eval a, v.i.eval a, v.j.eval a⟩

private theorem eval_rad {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) (k : Fin 2) :
    (fun e : Expr σ => e.eval a) (v.rad k) = Jones1982.Nine.rad (evalExprVars a v) k := by
  fin_cases k <;>
    simp [Expr.eval, RingVars.rad, Jones1982.Nine.rad, evalExprVars,
      RingVars.U, RingVars.Y, RingVars.M, RingVars.P, RingVars.K,
      RingVars.A, RingVars.B', RingVars.W, RingVars.C, RingVars.J,
      RingVars.D, RingVars.E, RingVars.F, RingVars.Gp,
      RingVars.H, RingVars.I,
      Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
      Jones1982.Nine.Vars.P, Jones1982.Nine.Vars.K, Jones1982.Nine.Vars.A,
      Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W, Jones1982.Nine.Vars.C,
      Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.D,
      Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F, Jones1982.Nine.Vars.Gp,
      Jones1982.Nine.Vars.H, Jones1982.Nine.Vars.I]

private theorem eval_wt {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) (k : Fin 2) :
    (v.wt k).eval a = Jones1982.Nine.wt (evalExprVars a v) k := by
  simp [RingVars.wt, Jones1982.Nine.wt, Expr.eval_pow, eval_rad, Expr.eval]

private theorem eval_dvsr {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) :
    (fun e : Expr σ => e.eval a) v.dvsr = Jones1982.Nine.dvsr (evalExprVars a v) := by
  simp [Expr.eval, RingVars.dvsr, Jones1982.Nine.dvsr, evalExprVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.A, RingVars.B', RingVars.W,
    RingVars.C, RingVars.J, RingVars.D, RingVars.E, RingVars.F,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.A, Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W,
    Jones1982.Nine.Vars.C, Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.D,
    Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F]

private theorem eval_dvnd {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) :
    (fun e : Expr σ => e.eval a) v.dvnd = Jones1982.Nine.dvnd (evalExprVars a v) := by
  simp [Expr.eval, RingVars.dvnd, Jones1982.Nine.dvnd, evalExprVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.A, RingVars.B', RingVars.W,
    RingVars.C, RingVars.J, RingVars.Q, RingVars.D, RingVars.E, RingVars.F, RingVars.H,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.A, Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W,
    Jones1982.Nine.Vars.C, Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.Q,
    Jones1982.Nine.Vars.D, Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F, Jones1982.Nine.Vars.H]

private theorem eval_marg {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) :
    (fun e : Expr σ => e.eval a) v.marg = Jones1982.Nine.marg (evalExprVars a v) := by
  simp [Expr.eval, RingVars.marg, Jones1982.Nine.marg, evalExprVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.P, RingVars.K,
    RingVars.B', RingVars.W, RingVars.C,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.P, Jones1982.Nine.Vars.K, Jones1982.Nine.Vars.B',
    Jones1982.Nine.Vars.W, Jones1982.Nine.Vars.C]

/-- Explicit syntax for every free Jones quantity. -/
noncomputable def syntaxVars (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (z y : ℕ) :
    RingVars (Expr (Fin 10)) :=
  let x : Expr (Fin 10) := .var 0
  let b := x * .constant (y : ℤ) + 1 + .var 1
  let q := (b ^ 5) ^ L4 ν
  let n := q ^ 16
  let e := univariate (epoly ν 4 P z) (b ^ 5)
  let l := univariate (lpoly ν 4) (b ^ 5)
  let lam := univariate (lampoly ν 4) (b ^ 5)
  let g : Expr (Fin 10) := .var 2 + 1
  let θ := b ^ 5 - 2 * .constant (z : ℤ)
  ⟨rankCode x (.constant (z : ℤ)) b e g l n q θ lam,
    n, b, g, 32 * b * (b ^ 5) ^ (5 ^ ν),
    .var 3 + 1, .var 4 + 1, .var 5 + 1, .var 6, .var 7 + 1, .var 8 + 1⟩

theorem eval_syntaxVars (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z y : ℕ) (a : Fin 10 → ℤ) :
    evalExprVars a (syntaxVars ν P z y) = Jones1982.Nine.varsOf ν P z y a := by
  simp [syntaxVars, evalExprVars, Jones1982.Nine.varsOf, rankCode, Jones1982.Nine.rZ,
    Expr.eval_pow, Expr.eval, eval_univariate]

/-- Syntax for the equation with its distinguished input still present. -/
noncomputable def withInput (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (z y : ℕ) :
    Expr (Fin 10) :=
  let v := syntaxVars ν P z y
  RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (.var 9)
    v.dvsr v.dvnd v.marg

theorem eval_withInput (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z y : ℕ) (a : Fin 10 → ℤ) :
    (withInput ν P z y).eval a = Jones1982.Nine.nineValue ν P z y a := by
  unfold Jones1982.Nine.nineValue
  rw [RefinedPair.value_eq]
  simp only [withInput, RefinedPair.value, Expr.eval_add, Expr.eval_sub, Expr.eval_mul,
    Expr.eval_pow, Expr.eval_var,
    eval_rad, eval_wt, eval_dvsr, eval_dvnd, eval_marg, eval_syntaxVars]
  rfl

/-- Replace the input by the fixed numeral 1 in the syntax itself. -/
def removeInput (e : Expr (Fin 10)) : Expr (Fin 9) :=
  e.subst (Fin.cons (.constant 1) (fun i => .var i))

theorem eval_removeInput (e : Expr (Fin 10)) (a : Fin 9 → ℤ) :
    (removeInput e).eval a = e.eval (Fin.cons 1 a) := by
  rw [removeInput, Expr.eval_subst]
  apply congrArg (fun f => e.eval f)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The complete nine-unknown arithmetic expression obtained from a quartic. -/
noncomputable def expression {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (bound : ℕ := 0) : Expr (Fin 9) :=
  removeInput (withInput ν P (JonesIndex.indexZ P bound) (JonesIndex.indexY P bound))

/-- The syntax and the explicit multivariate polynomial have equal values. -/
theorem eval_expression {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (bound : ℕ) (a : Fin 9 → ℤ) :
    (expression P bound).eval a = MvPolynomial.eval a (NinePolynomial.polynomial P bound) := by
  calc
    _ = Jones1982.Nine.nineValue ν P (JonesIndex.indexZ P bound) (JonesIndex.indexY P bound)
        (Fin.cons 1 a) := by
      rw [expression, eval_removeInput]
      exact eval_withInput _ _ _ _ _
    _ = _ := by
      symm
      calc
        _ = MvPolynomial.eval (Fin.cons 1 a)
            (NinePolynomial.withInput ν P (JonesIndex.indexZ P bound) (JonesIndex.indexY P bound)) :=
          eval_specializeOne _ _
        _ = _ := NinePolynomial.eval_withInput _ _ _ _ _

theorem hasNaturalZero_expression {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) (bound : ℕ) :
    (∃ a : Fin 9 → ℕ, (expression P bound).eval (fun i => (a i : ℤ)) = 0) ↔ Wset P 1 := by
  simpa only [eval_expression, HasNaturalZero] using
    NinePolynomial.hasNaturalZero_polynomial P hν hP hnorm bound

#print axioms hasNaturalZero_expression

end DiophantineConsistency.JonesSyntax
