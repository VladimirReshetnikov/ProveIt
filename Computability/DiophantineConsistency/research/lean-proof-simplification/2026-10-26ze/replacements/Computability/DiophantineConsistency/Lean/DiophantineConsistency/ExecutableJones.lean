import DiophantineConsistency.QuarticSyntax
import DiophantineConsistency.JonesSyntax

/-!
# Executable Jones arithmetic syntax from supplied quartic syntax

Finite monomial expansion supplies the coefficients. The coding polynomials
are emitted by their defining finite sums, rather than by noncomputable
polynomial coefficient or degree readers.
-/

namespace DiophantineConsistency.ExecutableJones

open Jones1982 NinePolynomial

@[simp] theorem eval_sumExpressions {σ : Type*} (es : List (Expr σ)) (v : σ → ℤ) :
    (QuarticSyntax.sumExpressions es).eval v = (es.map (Expr.eval v)).sum := by
  induction es <;> simp_all [QuarticSyntax.sumExpressions]

/-- Sum over a literal finite range; only syntax construction is involved. -/
def rangeSum {σ : Type*} (n : ℕ) (f : Fin n → Expr σ) : Expr σ :=
  QuarticSyntax.sumExpressions (List.ofFn f)

@[simp] theorem eval_rangeSum {σ : Type*} (n : ℕ) (f : Fin n → Expr σ) (v : σ → ℤ) :
    (rangeSum n f).eval v = ∑ i, (f i).eval v := by
  simp [rangeSum, List.map_ofFn, Fin.sum_ofFn]

/-- Explicit nested enumeration of all bounded exponent vectors. -/
def vectorSum {σ : Type*} : (n : ℕ) → ((Fin n → Fin 5) → Expr σ) → Expr σ
  | 0, f => f Fin.elim0
  | n + 1, f => rangeSum 5 fun a => vectorSum n fun b => f (Fin.cons a b)

@[simp] theorem eval_vectorSum {σ : Type*} (n : ℕ)
    (f : (Fin n → Fin 5) → Expr σ) (v : σ → ℤ) :
    (vectorSum n f).eval v = ∑ k, (f k).eval v := by
  induction n with
  | zero =>
    simp only [vectorSum, Fintype.sum_unique]
    exact congrArg (fun k => (f k).eval v) (Subsingleton.elim _ _)
  | succ n ih =>
    simp only [vectorSum, eval_rangeSum, ih]
    calc
      _ = ∑ p : Fin 5 × (Fin n → Fin 5), (f (Fin.cons p.1 p.2)).eval v :=
        (Fintype.sum_prod_type (fun p : Fin 5 × (Fin n → Fin 5) =>
          (f (Fin.cons p.1 p.2)).eval v)).symm
      _ = _ := Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Fin 5)
        (fun p => (f (Fin.cons p.1 p.2)).eval v) (fun k => (f k).eval v) (fun _ => rfl)

/-- Reindex the bounded-vector enumeration by the degree-four star. -/
theorem sum_bounded_eq_star {M : Type*} [AddCommMonoid M] (ν : ℕ)
    (f : (Fin (ν + 2) → ℕ) → M) :
    (∑ k : Fin (ν + 2) → Fin 5,
      if (∑ j, (k j : ℕ)) = 4 then f (fun j => (k j : ℕ)) else 0) =
      ∑ k ∈ star ν 4, f k := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ j => (k j : ℕ))
  · intro k hk
    exact (mem_star ν 4).2 (Finset.mem_filter.1 hk).2
  · intro a ha b hb h
    funext j
    exact Fin.ext (congrFun h j)
  · intro k hk
    let b : Fin (ν + 2) → Fin 5 := fun j => ⟨k j, by have := star_le ν 4 hk j; omega⟩
    refine ⟨b, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_star ν 4).1 hk⟩
  · intro k hk
    rfl

/-- Sum over the star with an explicit, executable order of its vectors. -/
def starSum {σ : Type*} (ν : ℕ) (f : (Fin (ν + 2) → ℕ) → Expr σ) : Expr σ :=
  vectorSum (ν + 2) fun k =>
    if (∑ j, (k j : ℕ)) = 4 then f (fun j => (k j : ℕ)) else .constant 0

@[simp] theorem eval_starSum {σ : Type*} (ν : ℕ)
    (f : (Fin (ν + 2) → ℕ) → Expr σ) (v : σ → ℤ) :
    (starSum ν f).eval v = ∑ k ∈ star ν 4, (f k).eval v := by
  rw [starSum, eval_vectorSum]
  simpa only [apply_ite, Expr.eval_constant] using
    sum_bounded_eq_star ν (fun k => (f k).eval v)

/-- The Jones coefficient, computed directly from the supplied syntax. -/
def pCoefficient {ν : ℕ} (e : Expr (Fin (ν + 1))) (k : Fin (ν + 2) → ℕ) : ℤ :=
  ((∏ j, (k j).factorial : ℕ) : ℤ) *
    SyntaxCoefficients.coefficient (SyntaxCoefficients.expand e) (fun j => k j.succ)

theorem pCoefficient_correct {ν : ℕ} (e : Expr (Fin (ν + 1)))
    (k : Fin (ν + 2) → ℕ) : pCoefficient e k = Pcoef ν e.toPolynomial k := by
  rw [pCoefficient, SyntaxCoefficients.coefficient_expand]
  rfl

def indexExponent {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) : ℕ :=
  bound + (∑ k ∈ star ν 4, (pCoefficient e k).natAbs) + 2

def indexZ {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) : ℕ :=
  2 ^ indexExponent e bound

theorem indexZ_correct {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) :
    indexZ e bound = JonesIndex.indexZ e.toPolynomial bound := by
  simp [indexZ, indexExponent, JonesIndex.indexZ, JonesIndex.indexExponent,
    JonesIndex.coefficientHeight, pCoefficient_correct]

def indexY {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) : ℕ :=
  (∑ k ∈ star ν 4,
    ((indexZ e bound : ℤ) + pCoefficient e k) *
      (2 * indexZ e bound : ℤ) ^ (Lexp ν 4 - expo ν 4 k)).toNat

theorem indexY_correct {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) :
    indexY e bound = JonesIndex.indexY e.toPolynomial bound := by
  simp [indexY, JonesIndex.indexY, eval_epoly, indexZ_correct, pCoefficient_correct]

/-- The coefficient encoding polynomial emitted by its literal star sum. -/
def eExpression {σ : Type*} {ν : ℕ} (e : Expr (Fin (ν + 1))) (z : ℕ) (B : Expr σ) :
    Expr σ :=
  starSum ν fun k =>
    .constant ((z : ℤ) + pCoefficient e k) * B ^ (Lexp ν 4 - expo ν 4 k)

@[simp] theorem eval_eExpression {σ : Type*} {ν : ℕ} (e : Expr (Fin (ν + 1)))
    (z : ℕ) (B : Expr σ) (v : σ → ℤ) :
    (eExpression e z B).eval v = (epoly ν 4 e.toPolynomial z).eval (B.eval v) := by
  simp [eExpression, eval_epoly, pCoefficient_correct]

/-- The fixed coding polynomial `l` emitted as a prefix sum. -/
def lExpression {σ : Type*} (B : Expr σ) : ℕ → Expr σ
  | 0 => .constant 0
  | n + 1 => lExpression B n + B ^ (5 ^ (n + 1))

@[simp] theorem eval_lExpression {σ : Type*} (B : Expr σ) (ν : ℕ) (v : σ → ℤ) :
    (lExpression B ν).eval v = (lpoly ν 4).eval (B.eval v) := by
  rw [eval_lpoly]
  induction ν with
  | zero => simp [lExpression]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    simp only [lExpression, Expr.eval_add, Expr.eval_pow, ih]

/-- The geometric coding polynomial `λ` emitted as a literal range sum. -/
def lamExpression {σ : Type*} (ν : ℕ) (B : Expr σ) : Expr σ :=
  rangeSum (4 * Lexp ν 4) fun i => B ^ (i : ℕ)

@[simp] theorem eval_lamExpression {σ : Type*} (ν : ℕ) (B : Expr σ) (v : σ → ℤ) :
    (lamExpression ν B).eval v = (lampoly ν 4).eval (B.eval v) := by
  simp [lamExpression, eval_lampoly, ← Fin.sum_univ_eq_sum_range]

/-- Every free Jones quantity, using only executable syntax constructors. -/
def syntaxVars {ν : ℕ} (seed : Expr (Fin (ν + 1))) (z y : ℕ) :
    RingVars (Expr (Fin 10)) :=
  let x : Expr (Fin 10) := .var 0
  let b := x * .constant (y : ℤ) + 1 + .var 1
  let q := (b ^ 5) ^ L4 ν
  let n := q ^ 16
  let e := eExpression seed z (b ^ 5)
  let l := lExpression (b ^ 5) ν
  let lam := lamExpression ν (b ^ 5)
  let g : Expr (Fin 10) := .var 2 + 1
  let θ := b ^ 5 - 2 * .constant (z : ℤ)
  ⟨rankCode x (.constant (z : ℤ)) b e g l n q θ lam,
    n, b, g, 32 * b * (b ^ 5) ^ (5 ^ ν),
    .var 3 + 1, .var 4 + 1, .var 5 + 1, .var 6, .var 7 + 1, .var 8 + 1⟩

theorem eval_syntaxVars {ν : ℕ} (seed : Expr (Fin (ν + 1)))
    (z y : ℕ) (a : Fin 10 → ℤ) :
    JonesSyntax.evalExprVars a (syntaxVars seed z y) =
      Jones1982.Nine.varsOf ν seed.toPolynomial z y a := by
  simp [syntaxVars, JonesSyntax.evalExprVars, Jones1982.Nine.varsOf,
    rankCode, Jones1982.Nine.rZ, Expr.eval_pow, Expr.eval]

def withInput {ν : ℕ} (seed : Expr (Fin (ν + 1))) (z y : ℕ) : Expr (Fin 10) :=
  let v := syntaxVars seed z y
  RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (.var 9)
    v.dvsr v.dvnd v.marg

theorem eval_withInput {ν : ℕ} (seed : Expr (Fin (ν + 1)))
    (z y : ℕ) (a : Fin 10 → ℤ) :
    (withInput seed z y).eval a = Jones1982.Nine.nineValue ν seed.toPolynomial z y a := by
  unfold Jones1982.Nine.nineValue
  rw [RefinedPair.value_eq]
  simp only [withInput, RefinedPair.value, Expr.eval_add, Expr.eval_sub, Expr.eval_mul,
    Expr.eval_pow, Expr.eval_var,
    JonesSyntax.eval_rad, JonesSyntax.eval_wt, JonesSyntax.eval_dvsr,
    JonesSyntax.eval_dvnd, JonesSyntax.eval_marg, eval_syntaxVars]
  rfl

/-- Executable nine-unknown syntax from a supplied seed expression. -/
def expression {ν : ℕ} (seed : Expr (Fin (ν + 1))) (bound : ℕ := 0) : Expr (Fin 9) :=
  JonesSyntax.removeInput (withInput seed (indexZ seed bound) (indexY seed bound))

theorem eval_expression {ν : ℕ} (seed : Expr (Fin (ν + 1)))
    (bound : ℕ) (a : Fin 9 → ℤ) :
    (expression seed bound).eval a =
      (JonesSyntax.expression seed.toPolynomial bound).eval a := by
  calc
    _ = Jones1982.Nine.nineValue ν seed.toPolynomial (indexZ seed bound)
        (indexY seed bound) (Fin.cons 1 a) := by
      rw [expression, JonesSyntax.eval_removeInput]
      exact eval_withInput _ _ _ _
    _ = _ := by
      rw [indexZ_correct, indexY_correct]
      symm
      rw [JonesSyntax.expression, JonesSyntax.eval_removeInput]
      exact JonesSyntax.eval_withInput _ _ _ _ _

theorem hasNaturalZero_expression {ν : ℕ} (seed : Expr (Fin (ν + 1)))
    (hν : 1 ≤ ν) (hP : seed.toPolynomial.totalDegree ≤ 4)
    (hnorm : Normalized seed.toPolynomial) (bound : ℕ) :
    (∃ a : Fin 9 → ℕ, (expression seed bound).eval (fun i => (a i : ℤ)) = 0) ↔
      Wset seed.toPolynomial 1 := by
  simpa only [eval_expression] using
    JonesSyntax.hasNaturalZero_expression seed.toPolynomial hν hP hnorm bound

/-- The entire syntax data path from a supplied representation is executable. -/
def fromRep {A : Prop} (r : Rep Empty (fun _ => A)) : Expr (Fin 9) :=
  expression (QuarticSyntax.expression r.expression.splitNatural.1 r.expression.splitNatural.2) 0

theorem eval_fromRep_polynomial {A : Prop} (r : Rep Empty (fun _ => A)) (a : Fin 9 → ℤ) :
    (fromRep r).eval a =
      MvPolynomial.eval a (NinePolynomial.polynomial (QuarticCompiler.compile r).polynomial 0) := by
  rw [fromRep, eval_expression, JonesSyntax.eval_expression, QuarticSyntax.polynomial_expression]
  rfl

theorem fromRep_correct {A : Prop} (r : Rep Empty (fun _ => A)) :
    (∃ a : Fin 9 → ℕ, (fromRep r).eval (fun i => (a i : ℤ)) = 0) ↔ A := by
  let p := r.expression.splitNatural.1
  let q := r.expression.splitNatural.2
  change (∃ a : Fin 9 → ℕ, (expression (QuarticSyntax.expression p q) 0).eval
    (fun i => (a i : ℤ)) = 0) ↔ A
  have hν : 1 ≤ QuarticCompiler.witnessCount p q := by
    dsimp only [QuarticCompiler.witnessCount]
    omega
  have hP : (QuarticSyntax.expression p q).toPolynomial.totalDegree ≤ 4 := by
    rw [QuarticSyntax.polynomial_expression]
    exact QuarticCompiler.quartic_degree p q
  have hnorm : Normalized (QuarticSyntax.expression p q).toPolynomial := by
    rw [QuarticSyntax.polynomial_expression]
    exact QuarticCompiler.quartic_normalized p q
  rw [hasNaturalZero_expression _ hν hP hnorm 0, QuarticSyntax.polynomial_expression]
  exact (QuarticCompiler.wset_quartic_iff p q 1).trans
    (r.correct_splitNatural Empty.elim).symm

theorem noZero_fromRep {A : Prop} (r : Rep Empty (fun _ => A)) :
    (¬ ∃ a : Fin 9 → ℕ, (fromRep r).eval (fun i => (a i : ℤ)) = 0) ↔ ¬ A :=
  not_congr (fromRep_correct r)

theorem hasNaturalZero_fromRep_polynomial {A : Prop} (r : Rep Empty (fun _ => A)) :
    HasNaturalZero (fromRep r).toPolynomial ↔ A := by
  simpa only [HasNaturalZero, Expr.eval_toPolynomial] using fromRep_correct r

#print axioms indexY_correct
#print axioms noZero_fromRep

end DiophantineConsistency.ExecutableJones
