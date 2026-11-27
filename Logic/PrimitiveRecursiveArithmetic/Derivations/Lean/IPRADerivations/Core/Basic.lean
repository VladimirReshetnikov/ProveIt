import ConciseIPRA.PR
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Basic arithmetic symbols of iPRA and their defining equations

This file fixes primitive recursive symbols for addition, multiplication,
predecessor and truncated subtraction, writes the corresponding term
operations as `+`, `*`, `pred` and `monus` on `PTm n`, and derives their
defining equations in `Prf PRAAx` at arbitrary argument terms.

It also packages two structural tools used throughout:

* `ind`, quantifier-free induction on variable `0` for an open formula, with
  the other free variables as parameters;
* `inst`, instantiation of the free variables of a closed derivation by
  arbitrary terms under arbitrary hypotheses.

Everything here is a derivation in the embedded calculus `Prf PRAAx` of
`ConciseIPRA`; no axiom beyond `PRAAx` is used.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-! ## Symbols -/

namespace Sym

/-- The constant `0` of arity `k`. -/
def zeroK (k : ℕ) : PR k := .comp .zero Fin.elim0

/-- Addition, by recursion on the first argument: `0 + x = x`, `S y + x = S (y + x)`. -/
def add : PR 2 := .prec (.proj 0) (.comp .succ (fun _ => .proj 1))

/-- Multiplication, by recursion on the first argument:
`0 * x = 0`, `S y * x = y * x + x`. -/
def mul : PR 2 := .prec (zeroK 1) (.comp add ![.proj 1, .proj 2])

/-- Predecessor: `pred 0 = 0`, `pred (S y) = y`. -/
def pred : PR 1 := .prec .zero (.proj 0)

/-- Truncated subtraction with the subtrahend first:
`rsub 0 x = x`, `rsub (S y) x = pred (rsub y x)`. -/
def rsub : PR 2 := .prec (.proj 0) (.comp pred ![.proj 1])

end Sym

/-! ## Term operations -/

namespace PTm

variable {n m : ℕ}

instance : Add (PTm n) := ⟨fun a b => .app Sym.add ![a, b]⟩
instance : Mul (PTm n) := ⟨fun a b => .app Sym.mul ![a, b]⟩

/-- Predecessor of a term. -/
def pred (a : PTm n) : PTm n := .app Sym.pred ![a]

/-- Truncated subtraction `a ∸ b`. -/
def monus (a b : PTm n) : PTm n := .app Sym.rsub ![b, a]

/-- The numeral `k`. -/
def num : ℕ → PTm n
  | 0 => ConciseIPRA.PTm.zero
  | k + 1 => ConciseIPRA.PTm.succ (num k)

theorem add_def (a b : PTm n) : a + b = .app Sym.add ![a, b] := rfl
theorem mul_def (a b : PTm n) : a * b = .app Sym.mul ![a, b] := rfl

@[simp] theorem subst_add (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (a + b) = Syn.subst σ a + Syn.subst σ b := by
  show ConciseIPRA.PTm.app _ _ = ConciseIPRA.PTm.app _ _
  congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem subst_mul (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (a * b) = Syn.subst σ a * Syn.subst σ b := by
  show ConciseIPRA.PTm.app _ _ = ConciseIPRA.PTm.app _ _
  congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem subst_pred (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (pred a) = pred (Syn.subst σ a) := by
  show ConciseIPRA.PTm.app _ _ = ConciseIPRA.PTm.app _ _
  congr 1; funext i; fin_cases i; rfl

@[simp] theorem subst_monus (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (monus a b) = monus (Syn.subst σ a) (Syn.subst σ b) := by
  show ConciseIPRA.PTm.app _ _ = ConciseIPRA.PTm.app _ _
  congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem subst_num (σ : Fin n → PTm m) (k : ℕ) :
    Syn.subst σ (num k : PTm n) = num k := by
  induction k with
  | zero => exact ConciseIPRA.PTm.subst_zero σ
  | succ k ih => simp [num, ih]

end PTm

open ConciseIPRA.PTm (app zero succ)
open PTm (pred monus num)

/-! ## Substitutions at numeral indices

`Syn.repl_succ` and `Syn.inst_succ` are stated for `Fin.succ i`; `simp` writes small
indices as numerals, so the instances at numerals are recorded here. -/

section Numerals

variable {n : ℕ}

@[simp] theorem repl_one (s : PTm (n + 2)) : repl s 1 = (var 1 : PTm (n + 2)) := repl_succ s 0
@[simp] theorem repl_two (s : PTm (n + 3)) : repl s 2 = (var 2 : PTm (n + 3)) := repl_succ s 1
@[simp] theorem repl_three (s : PTm (n + 4)) : repl s 3 = (var 3 : PTm (n + 4)) :=
  repl_succ s 2
@[simp] theorem repl_four (s : PTm (n + 5)) : repl s 4 = (var 4 : PTm (n + 5)) :=
  repl_succ s 3
@[simp] theorem inst_two (t : PTm (n + 2)) : Syn.inst t 2 = (var 1 : PTm (n + 2)) :=
  inst_succ t 1
@[simp] theorem inst_three (t : PTm (n + 3)) : Syn.inst t 3 = (var 2 : PTm (n + 3)) :=
  inst_succ t 2
@[simp] theorem inst_four (t : PTm (n + 4)) : Syn.inst t 4 = (var 3 : PTm (n + 4)) :=
  inst_succ t 3

@[simp] theorem finCases_two {α : Sort _} (a : α) (f : Fin (n + 2) → α) :
    (Fin.cases a f : Fin (n + 3) → α) 2 = f 1 := rfl
@[simp] theorem finCases_three {α : Sort _} (a : α) (f : Fin (n + 3) → α) :
    (Fin.cases a f : Fin (n + 4) → α) 3 = f 2 := rfl
@[simp] theorem finCases_four {α : Sort _} (a : α) (f : Fin (n + 4) → α) :
    (Fin.cases a f : Fin (n + 5) → α) 4 = f 3 := rfl
@[simp] theorem finCases_five {α : Sort _} (a : α) (f : Fin (n + 5) → α) :
    (Fin.cases a f : Fin (n + 6) → α) 5 = f 4 := rfl

@[simp] theorem fin_succ_two : (Fin.succ (2 : Fin (n + 3)) : Fin (n + 4)) = 3 := rfl
@[simp] theorem fin_succ_three : (Fin.succ (3 : Fin (n + 4)) : Fin (n + 5)) = 4 := rfl

end Numerals

/-! ## Structural tools -/

section Tools

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- A closed derivation over `k` free variables, instantiated by arbitrary terms
under arbitrary hypotheses. -/
theorem inst {φ : Fm PTm k} (h : ([] : List (Fm PTm k)) ⊢[PRAAx] φ) (σ : Fin k → PTm n) :
    Γ ⊢[PRAAx] φ.subst σ := by
  have h' := h.subst σ
  simp only [List.map_nil] at h'
  exact h'.ofNil

/-- Quantifier-free induction on variable `0` of an open formula, the other free
variables being parameters. -/
theorem ind (φ : Fm PTm (k + 1)) (hφ : φ.QF)
    (h0 : ([] : List (Fm PTm k)) ⊢[PRAAx] φ.subst (Syn.inst zero))
    (hS : [φ] ⊢[PRAAx] φ.subst (repl (succ (var 0)))) :
    ([] : List (Fm PTm (k + 1))) ⊢[PRAAx] φ := by
  have h := PRA.qfInd φ hφ h0 (by simpa using hS)
  simpa using h.allOpen

/-- The third hypothesis. -/
theorem hyp2 {φ ψ χ : Fm PTm n} : (χ :: ψ :: φ :: Γ) ⊢[PRAAx] φ := .hyp (by simp)

/-- Congruence of a function symbol. -/
theorem congrApp {j : ℕ} (f : PR j) {ts us : Fin j → PTm n}
    (h : ∀ i, Γ ⊢[PRAAx] ts i ≐ us i) : Γ ⊢[PRAAx] app f ts ≐ app f us := by
  simpa using Prf.eqCongr (app f var) h

theorem congrSucc {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] succ a ≐ succ b :=
  congrApp .succ fun _ => h

theorem congrAdd {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ b) (h₂ : Γ ⊢[PRAAx] c ≐ d) :
    Γ ⊢[PRAAx] a + c ≐ b + d :=
  congrApp Sym.add fun i => by fin_cases i <;> assumption

theorem congrMul {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ b) (h₂ : Γ ⊢[PRAAx] c ≐ d) :
    Γ ⊢[PRAAx] a * c ≐ b * d :=
  congrApp Sym.mul fun i => by fin_cases i <;> assumption

theorem congrPred {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] pred a ≐ pred b :=
  congrApp Sym.pred fun i => by fin_cases i; exact h

theorem congrMonus {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ b) (h₂ : Γ ⊢[PRAAx] c ≐ d) :
    Γ ⊢[PRAAx] monus a c ≐ monus b d :=
  congrApp Sym.rsub fun i => by fin_cases i <;> assumption

end Tools

/-! ## Defining equations -/

section Equations

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zeroK_eq {k : ℕ} (ts : Fin k → PTm n) : Γ ⊢[PRAAx] app (Sym.zeroK k) ts ≐ zero := by
  have h := PRA.comp (Γ := Γ) PR.zero Fin.elim0 ts
  have e : (fun j : Fin 0 => app ((Fin.elim0 j : PR k)) ts) = Fin.elim0 :=
    funext fun j => j.elim0
  rw [e] at h
  exact h

theorem zero_add (b : PTm n) : Γ ⊢[PRAAx] zero + b ≐ b :=
  .eqTrans (PRA.precZero (Γ := Γ) (.proj 0) _ ![b]) (PRA.proj (Γ := Γ) 0 ![b])

theorem succ_add (a b : PTm n) : Γ ⊢[PRAAx] succ a + b ≐ succ (a + b) := by
  refine .eqTrans (PRA.precSucc (Γ := Γ) (.proj 0) _ a ![b]) ?_
  refine .eqTrans (PRA.comp _ _ _) ?_
  exact congrSucc (PRA.proj _ _)

theorem zero_mul (b : PTm n) : Γ ⊢[PRAAx] zero * b ≐ zero :=
  .eqTrans (PRA.precZero (Γ := Γ) (Sym.zeroK 1) _ ![b]) (zeroK_eq _)

theorem succ_mul (a b : PTm n) : Γ ⊢[PRAAx] succ a * b ≐ a * b + b := by
  refine .eqTrans (PRA.precSucc (Γ := Γ) (Sym.zeroK 1) _ a ![b]) ?_
  refine .eqTrans (PRA.comp _ _ _) ?_
  exact congrApp Sym.add fun i => by
    fin_cases i
    · exact PRA.proj _ _
    · exact PRA.proj _ _

theorem pred_zero : Γ ⊢[PRAAx] pred (zero : PTm n) ≐ zero :=
  PRA.precZero .zero (.proj 0) ![]

theorem pred_succ (a : PTm n) : Γ ⊢[PRAAx] pred (succ a) ≐ a :=
  (PRA.precSucc .zero (.proj 0) a ![]).eqTrans (PRA.proj _ _)

theorem monus_zero (a : PTm n) : Γ ⊢[PRAAx] monus a zero ≐ a :=
  .eqTrans (PRA.precZero (Γ := Γ) (.proj 0) _ ![a]) (PRA.proj (Γ := Γ) 0 ![a])

theorem monus_succ (a b : PTm n) : Γ ⊢[PRAAx] monus a (succ b) ≐ pred (monus a b) := by
  refine .eqTrans (PRA.precSucc (Γ := Γ) (.proj 0) _ b ![a]) ?_
  refine .eqTrans (PRA.comp _ _ _) ?_
  exact congrApp Sym.pred fun i => by fin_cases i; exact PRA.proj _ _

end Equations

end LeanProofs.IPRA
