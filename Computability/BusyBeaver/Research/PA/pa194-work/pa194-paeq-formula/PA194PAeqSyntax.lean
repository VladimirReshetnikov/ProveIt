import Foundation.FirstOrder.Arithmetic.Basic.Misc
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq
open LO LO.FirstOrder

inductive Func : Nat → Type
  | zero : Func 0
  | succ : Func 1
  | add : Func 2
  | mul : Func 2
inductive Rel : Nat → Type
  | eq : Rel 2

@[reducible] def language : Language where
  Func := Func
  Rel := Rel

def zero {ξ : Type} {n : Nat} : Semiterm language ξ n := .func .zero Fin.elim0
def succ {ξ : Type} {n : Nat} (t : Semiterm language ξ n) : Semiterm language ξ n :=
  .func .succ ![t]
def add {ξ : Type} {n : Nat} (s t : Semiterm language ξ n) : Semiterm language ξ n :=
  .func .add ![s,t]
def mul {ξ : Type} {n : Nat} (s t : Semiterm language ξ n) : Semiterm language ξ n :=
  .func .mul ![s,t]
def eq {ξ : Type} {n : Nat} (s t : Semiterm language ξ n) : Semiformula language ξ n :=
  .rel .eq ![s,t]

def term {ξ : Type} {n : Nat} : ArithmeticSemiterm ξ n → Semiterm language ξ n
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .func .zero _ => zero
  | .func .one _ => succ zero
  | .func .add ts => add (term (ts 0)) (term (ts 1))
  | .func .mul ts => mul (term (ts 0)) (term (ts 1))

/-- Strict order is defined by a positive additive difference, not nonstrict order. -/
def less {ξ : Type} {n : Nat} (s t : Semiterm language ξ n) : Semiformula language ξ n :=
  .exs (eq (add (Rew.bShift s) (succ (.bvar 0))) (Rew.bShift t))

def atom {ξ : Type} {n k : Nat} (r : Language.ORing.Rel k)
    (ts : Fin k → ArithmeticSemiterm ξ n) : Semiformula language ξ n :=
  match r with
  | .eq => eq (term (ts 0)) (term (ts 1))
  | .lt => less (term (ts 0)) (term (ts 1))

def formula {ξ : Type} : {n : Nat} → ArithmeticSemiformula ξ n → Semiformula language ξ n
  | _,.verum => .verum
  | _,.falsum => .falsum
  | _,.rel r ts => atom r ts
  | _,.nrel r ts => (atom r ts).neg
  | _,.and p q => .and (formula p) (formula q)
  | _,.or p q => .or (formula p) (formula q)
  | _,.all p => .all (formula p)
  | _,.exs p => .exs (formula p)

@[simp] theorem formula_neg {ξ : Type} {n : Nat} (p : ArithmeticSemiformula ξ n) :
    formula p.neg = (formula p).neg := by
  induction p <;> simp [formula,Semiformula.neg,Semiformula.neg_neg, *]

@[simp] theorem formula_falsum {ξ : Type} {n : Nat} :
    formula (.falsum : ArithmeticSemiformula ξ n) = .falsum := rfl

@[simp] theorem rew_zero {ξ ζ : Type} {n m : Nat} (τ : Rew language ξ n ζ m) :
    τ zero = zero := by
  change τ (.func Func.zero Fin.elim0) = .func Func.zero Fin.elim0
  rw [τ.func']
  apply congrArg (Semiterm.func (L := language) (ξ := ζ) (n := m) Func.zero)
  funext i
  exact Fin.elim0 i

@[simp] theorem rew_succ {ξ ζ : Type} {n m : Nat} (τ : Rew language ξ n ζ m)
    (t : Semiterm language ξ n) : τ (succ t) = succ (τ t) := by
  change τ (.func Func.succ ![t]) = .func Func.succ ![τ t]
  rw [τ.func']
  apply congrArg (Semiterm.func (L := language) (ξ := ζ) (n := m) Func.succ)
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

@[simp] theorem rew_add {ξ ζ : Type} {n m : Nat} (τ : Rew language ξ n ζ m)
    (s t : Semiterm language ξ n) : τ (add s t) = add (τ s) (τ t) := by
  change τ (.func Func.add ![s,t]) = .func Func.add ![τ s,τ t]
  rw [τ.func']
  apply congrArg (Semiterm.func (L := language) (ξ := ζ) (n := m) Func.add)
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

@[simp] theorem rew_mul {ξ ζ : Type} {n m : Nat} (τ : Rew language ξ n ζ m)
    (s t : Semiterm language ξ n) : τ (mul s t) = mul (τ s) (τ t) := by
  change τ (.func Func.mul ![s,t]) = .func Func.mul ![τ s,τ t]
  rw [τ.func']
  apply congrArg (Semiterm.func (L := language) (ξ := ζ) (n := m) Func.mul)
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

/-- Compatibility for arbitrary paired substitutions, including term-valued ones. -/
theorem term_rew {ξ ζ : Type} {n m : Nat} (ω : Rew ℒₒᵣ ξ n ζ m)
    (τ : Rew language ξ n ζ m)
    (hb : ∀ i,term (ω (.bvar i)) = τ (.bvar i))
    (hf : ∀ i,term (ω (.fvar i)) = τ (.fvar i))
    (t : ArithmeticSemiterm ξ n) : term (ω t) = τ (term t) := by
  induction t with
  | bvar i => exact hb i
  | fvar i => exact hf i
  | func f ts ih =>
    cases f <;> simp only [ω.func,term,Function.comp_apply,ih,rew_zero,rew_succ,rew_add,rew_mul]

#print axioms formula_neg
#print axioms term_rew
end PA194PAeq

