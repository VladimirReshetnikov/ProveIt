import IPRADerivations.Core.Tactic

/-!
# Explicit and recursive definitions in iPRA

* `PTm.toPR e` is the primitive recursive symbol computing an open term `e`
  (composition of projections), with `toPR_eq : app (toPR e) ts ≐ e[ts]`.
* `recDef base step` is the symbol defined by primitive recursion from a base
  term and a step term, with defining equations `rec_zero` and `rec_succ` stated
  as substitutions into those terms.
* From these: finite sums `∑_{i<y} body(i, x⃗)` and products, powers and the
  factorial, each with its two equations at arbitrary terms.

These give readable iPRA definitions of the sequences used in the packets, and
an equation for each step that the induction proofs below feed to the ring tools.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Explicit definitions -/

/-- The symbol computing an open term. -/
def PTm.toPR {k : ℕ} : PTm k → PR k
  | .var i => .proj i
  | .app f ts => .comp f fun j => PTm.toPR (ts j)

theorem toPR_eq {k : ℕ} (e : PTm k) (ts : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (PTm.toPR e) ts ≐ Syn.subst ts e := by
  induction e with
  | var i => simpa [PTm.toPR] using PRA.proj (Γ := Γ) i ts
  | app f es ih => exact (PRA.comp f _ ts).eqTrans (congrApp f ih)

/-! ## Definitions by primitive recursion -/

/-- `h(0, x⃗) = base(x⃗)`, `h(y + 1, x⃗) = step(y, h(y, x⃗), x⃗)`. -/
def recDef {k : ℕ} (base : PTm k) (step : PTm (k + 2)) : PR (k + 1) :=
  .prec (PTm.toPR base) (PTm.toPR step)

theorem rec_zero {k : ℕ} (base : PTm k) (step : PTm (k + 2)) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (recDef base step) (Fin.cases zero xs) ≐ Syn.subst xs base :=
  (PRA.precZero _ _ xs).eqTrans (toPR_eq base xs)

theorem rec_succ {k : ℕ} (base : PTm k) (step : PTm (k + 2)) (y : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] app (recDef base step) (Fin.cases (succ y) xs)
      ≐ Syn.subst (Fin.cases y (Fin.cases (app (recDef base step) (Fin.cases y xs)) xs)) step :=
  (PRA.precSucc _ _ y xs).eqTrans (toPR_eq step _)

/-! ## Unary and binary application -/

/-- `f(a)`. -/
def ap1 (f : PR 1) (a : PTm n) : PTm n := app f ![a]
/-- `f(a, b)`. -/
def ap2 (f : PR 2) (a b : PTm n) : PTm n := app f ![a, b]

@[simp] theorem subst_ap1 {m : ℕ} (σ : Fin n → PTm m) (f : PR 1) (a : PTm n) :
    Syn.subst σ (ap1 f a) = ap1 f (Syn.subst σ a) := by
  show app _ _ = app _ _; congr 1; funext i; fin_cases i; rfl

@[simp] theorem subst_ap2 {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (a b : PTm n) :
    Syn.subst σ (ap2 f a b) = ap2 f (Syn.subst σ a) (Syn.subst σ b) := by
  show app _ _ = app _ _; congr 1; funext i; fin_cases i <;> rfl

theorem congrAp1 (f : PR 1) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] ap1 f a ≐ ap1 f b :=
  congrApp f fun i => by fin_cases i; exact h

theorem congrAp2 (f : PR 2) {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ b) (h₂ : Γ ⊢[PRAAx] c ≐ d) :
    Γ ⊢[PRAAx] ap2 f a c ≐ ap2 f b d :=
  congrApp f fun i => by fin_cases i <;> assumption

/-- A unary recursion `h(0) = c`, `h(y + 1) = step(y, h(y))`. -/
def rec1 (c : PTm 0) (step : PTm 2) : PR 1 := recDef c step

theorem rec1_zero (c : PTm 0) (step : PTm 2) :
    Γ ⊢[PRAAx] ap1 (rec1 c step) zero ≐ Syn.subst Fin.elim0 c := by
  have h := rec_zero (Γ := Γ) c step (Fin.elim0 : Fin 0 → PTm n)
  have e : (Fin.cases zero Fin.elim0 : Fin 1 → PTm n) = ![zero] := by funext i; fin_cases i; rfl
  rw [e] at h; exact h

theorem rec1_succ (c : PTm 0) (step : PTm 2) (y : PTm n) :
    Γ ⊢[PRAAx] ap1 (rec1 c step) (succ y) ≐ Syn.subst ![y, ap1 (rec1 c step) y] step := by
  have h := rec_succ (Γ := Γ) c step y (Fin.elim0 : Fin 0 → PTm n)
  have e₁ : (Fin.cases (succ y) Fin.elim0 : Fin 1 → PTm n) = ![succ y] := by
    funext i; fin_cases i; rfl
  have e₂ : (Fin.cases y Fin.elim0 : Fin 1 → PTm n) = ![y] := by funext i; fin_cases i; rfl
  have e₃ : (Fin.cases y (Fin.cases (app (recDef c step) ![y]) Fin.elim0) : Fin 2 → PTm n)
      = ![y, ap1 (rec1 c step) y] := by funext i; fin_cases i <;> rfl
  rw [e₁, e₂, e₃] at h; exact h

/-- A binary recursion on the first argument with one parameter:
`h(0, x) = base(x)`, `h(y + 1, x) = step(y, h(y, x), x)`. -/
def rec2 (base : PTm 1) (step : PTm 3) : PR 2 := recDef base step

theorem rec2_zero (base : PTm 1) (step : PTm 3) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (rec2 base step) zero x ≐ Syn.subst ![x] base := by
  have h := rec_zero (Γ := Γ) base step ![x]
  exact h

theorem rec2_succ (base : PTm 1) (step : PTm 3) (y x : PTm n) :
    Γ ⊢[PRAAx] ap2 (rec2 base step) (succ y) x
      ≐ Syn.subst ![y, ap2 (rec2 base step) y x, x] step := by
  have h := rec_succ (Γ := Γ) base step y ![x]
  have e : (Fin.cases y (Fin.cases (app (recDef base step) (Fin.cases y ![x])) ![x]) : Fin 3 → PTm n)
      = ![y, ap2 (rec2 base step) y x, x] := by funext i; fin_cases i <;> rfl
  rw [e] at h; exact h

/-- Read an application in a binary recursion's successor step using its substituted arguments. -/
theorem rec2_succ_app {k : ℕ} (base : PTm 1) (f : PR k) (args : Fin k → PTm 3)
    (y x : PTm n) (values : Fin k → PTm n)
    (read : (fun i => Syn.subst ![y, ap2 (rec2 base (app f args)) y x, x] (args i)) = values) :
    Γ ⊢[PRAAx] ap2 (rec2 base (app f args)) (succ y) x ≐ app f values := by
  refine (rec2_succ base (app f args) y x).eqTrans ?_
  rw [PTm.subst_app, read]
  exact .eqRefl _

/-! ## Sums, products, powers and factorials -/

/-- The parameter-preserving renaming used to put a body under the recursion
variable and the accumulator: `0 ↦ 0`, `1 ↦ 2`. -/
def bodyStep (body : PTm 2) : PTm 3 := Syn.subst ![var 0, var 2] body

/-- `S(y, x) = ∑_{i<y} body(i, x)`. -/
def sumF (body : PTm 2) : PR 2 := rec2 zero (var 1 + bodyStep body)

/-- `P(y, x) = ∏_{i<y} body(i, x)`. -/
def prodF (body : PTm 2) : PR 2 := rec2 (succ zero) (var 1 * bodyStep body)

theorem sum_zero (body : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF body) zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (var 1 + bodyStep body) x
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem sum_succ (body : PTm 2) (y x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF body) (succ y) x ≐ ap2 (sumF body) y x + Syn.subst ![y, x] body := by
  have h := rec2_succ (Γ := Γ) zero (var 1 + bodyStep body) y x
  have e : Syn.subst ![y, ap2 (sumF body) y x, x] (var 1 + bodyStep body)
      = ap2 (sumF body) y x + Syn.subst ![y, x] body := by
    rw [PTm.subst_add, bodyStep, Syn.subst_subst]
    exact congrArg₂ (· + ·) rfl (congrArg (fun σ => Syn.subst σ body) (by funext i; fin_cases i <;> rfl))
  exact e ▸ h

theorem prod_zero (body : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF body) zero x ≐ succ zero := by
  have h := rec2_zero (Γ := Γ) (succ zero) (var 1 * bodyStep body) x
  simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem prod_succ (body : PTm 2) (y x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF body) (succ y) x ≐ ap2 (prodF body) y x * Syn.subst ![y, x] body := by
  have h := rec2_succ (Γ := Γ) (succ zero) (var 1 * bodyStep body) y x
  have e : Syn.subst ![y, ap2 (prodF body) y x, x] (var 1 * bodyStep body)
      = ap2 (prodF body) y x * Syn.subst ![y, x] body := by
    rw [PTm.subst_mul, bodyStep, Syn.subst_subst]
    exact congrArg₂ (· * ·) rfl (congrArg (fun σ => Syn.subst σ body) (by funext i; fin_cases i <;> rfl))
  exact e ▸ h

/-- `pow(y, x) = xʸ`. -/
def powF : PR 2 := prodF (var 1)

theorem pow_zero' (x : PTm n) : Γ ⊢[PRAAx] ap2 powF zero x ≐ succ zero := prod_zero _ x

theorem pow_succ' (y x : PTm n) : Γ ⊢[PRAAx] ap2 powF (succ y) x ≐ ap2 powF y x * x := by
  have h := prod_succ (Γ := Γ) (var 1) y x
  simp only [Syn.subst_var] at h
  exact h

/-- `fact(y) = y!`, with a dummy parameter. -/
def factF : PR 2 := prodF (succ (var 0))

theorem fact_zero (x : PTm n) : Γ ⊢[PRAAx] ap2 factF zero x ≐ succ zero := prod_zero _ x

theorem fact_succ (y x : PTm n) : Γ ⊢[PRAAx] ap2 factF (succ y) x ≐ ap2 factF y x * succ y := by
  have h := prod_succ (Γ := Γ) (succ (var 0)) y x
  simp only [ConciseIPRA.PTm.subst_succ, Syn.subst_var] at h
  exact h

end LeanProofs.IPRA
