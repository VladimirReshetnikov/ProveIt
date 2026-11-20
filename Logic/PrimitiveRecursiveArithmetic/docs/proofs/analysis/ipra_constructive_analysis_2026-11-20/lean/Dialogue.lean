import Std

/-!
An oracle may give a different type of answer at each address. The semantic
tree can branch infinitely. A uniform bound is separate data. The numerical
machine near the end is the interface for the primitive-recursive fragment.
-/
namespace BudgetAnalysis

inductive Dialogue (Q : Type) (A : Q → Type) (R : Type) : Type where
  | ret (r : R)
  | ask (q : Q) (next : A q → Dialogue Q A R)

namespace Dialogue
variable {Q P R S : Type} {A : Q → Type} {B : P → Type}

def eval (o : (q : Q) → A q) : Dialogue Q A R → R
  | .ret r => r
  | .ask q next => eval o (next (o q))

def trace (o : (q : Q) → A q) : Dialogue Q A R → List Q
  | .ret _ => []
  | .ask q next => q :: trace o (next (o q))

/-- A tree halts after at most the supplied number of requests on every branch. -/
inductive Bounded : Dialogue Q A R → Nat → Prop where
  | ret (r : R) (n : Nat) : Bounded (.ret r) n
  | ask (q : Q) (next : A q → Dialogue Q A R) (n : Nat)
      (rest : ∀ a, Bounded (next a) n) : Bounded (.ask q next) (n + 1)

theorem trace_length_le {t : Dialogue Q A R} {n : Nat}
    (h : Bounded t n) (o : (q : Q) → A q) : (trace o t).length ≤ n := by
  induction h with
  | ret => exact Nat.zero_le _
  | ask q next n rest ih => exact Nat.succ_le_succ (ih (o q))

/-- Only the first run determines the addresses on which agreement is needed. -/
theorem replay (t : Dialogue Q A R) (o p : (q : Q) → A q)
    (agree : ∀ q ∈ trace o t, o q = p q) :
    eval o t = eval p t ∧ trace o t = trace p t := by
  induction t with
  | ret r => exact ⟨rfl, rfl⟩
  | ask q next ih =>
    have atHead : o q = p q := agree q (by simp [trace])
    have atTail : ∀ i ∈ trace o (next (o q)), o i = p i :=
      fun i hi => agree i (by simp [trace, hi])
    obtain ⟨valEq, traceEq⟩ := ih (o q) atTail
    simp only [eval, trace, ← atHead]
    exact ⟨valEq, congrArg (List.cons q) traceEq⟩

def bind (t : Dialogue Q A R) (f : R → Dialogue Q A S) : Dialogue Q A S :=
  match t with
  | .ret r => f r
  | .ask q next => .ask q (fun a => bind (next a) f)

theorem eval_bind (t : Dialogue Q A R) (f : R → Dialogue Q A S)
    (o : (q : Q) → A q) : eval o (bind t f) = eval o (f (eval o t)) := by
  induction t with
  | ret => rfl
  | ask q next ih => exact ih (o q)

theorem trace_bind (t : Dialogue Q A R) (f : R → Dialogue Q A S)
    (o : (q : Q) → A q) :
    trace o (bind t f) = trace o t ++ trace o (f (eval o t)) := by
  induction t with
  | ret => rfl
  | ask q next ih => exact congrArg (List.cons q) (ih (o q))

theorem bounded_bind {t : Dialogue Q A R} {n k : Nat}
    (ht : Bounded t n) (f : R → Dialogue Q A S) (hf : ∀ r, Bounded (f r) k) :
    Bounded (bind t f) (n + k) := by
  induction ht with
  | ret r n =>
    have weaken {v : Dialogue Q A S} {m : Nat} (hv : Bounded v m) :
        Bounded v (n + m) := by
      induction hv with
      | ret => exact Bounded.ret _ _
      | ask q next m rest ih => exact Bounded.ask q next (n + m) ih
    exact weaken (hf r)
  | ask q next n rest ih =>
    rw [Nat.succ_add]
    exact Bounded.ask q _ _ ih

/-- Implement each outer request by a dialogue over a new input interface. -/
def subst (g : (q : Q) → Dialogue P B (A q)) : Dialogue Q A R → Dialogue P B R
  | .ret r => .ret r
  | .ask q next => bind (g q) (fun a => subst g (next a))

theorem eval_subst (t : Dialogue Q A R) (g : (q : Q) → Dialogue P B (A q))
    (o : (p : P) → B p) :
    eval o (subst g t) = eval (fun q => eval o (g q)) t := by
  induction t with
  | ret => rfl
  | ask q next ih => simpa only [subst, eval_bind, eval] using ih (eval o (g q))

/-- The list is ordered, and includes repeated requests. -/
theorem trace_subst (t : Dialogue Q A R) (g : (q : Q) → Dialogue P B (A q))
    (o : (p : P) → B p) :
    trace o (subst g t) =
      (trace (fun q => eval o (g q)) t).flatMap (fun q => trace o (g q)) := by
  induction t with
  | ret => rfl
  | ask q next ih =>
    simp only [subst, trace_bind, trace, List.flatMap_cons, ih]

theorem bounded_subst {t : Dialogue Q A R} {n k : Nat} (ht : Bounded t n)
    (g : (q : Q) → Dialogue P B (A q)) (hg : ∀ q, Bounded (g q) k) :
    Bounded (subst g t) (n * k) := by
  induction ht with
  | ret => exact Bounded.ret _ _
  | ask q next n rest ih =>
    rw [Nat.succ_mul, Nat.add_comm]
    exact bounded_bind (hg q) _ ih
end Dialogue

/-- Individual transitions of an arithmetic instance must have fixed PR definitions. -/
structure QueryMachine where
  halted : Nat → Bool
  out : Nat → Nat
  address : Nat → Nat
  advance : Nat → Nat → Nat

abbrev NumDialogue := Dialogue Nat (fun _ => Nat) (Option Nat)

/-- Check for a final value even when the last available query has been consumed. -/
def QueryMachine.cut (M : QueryMachine) : Nat → Nat → NumDialogue
  | 0, s => .ret (if M.halted s then some (M.out s) else none)
  | n+1, s =>
    if M.halted s then .ret (some (M.out s))
    else .ask (M.address s) (fun a => M.cut n (M.advance s a))

theorem QueryMachine.cut_bound (M : QueryMachine) (n s : Nat) :
    Dialogue.Bounded (M.cut n s) n := by
  induction n generalizing s with
  | zero => exact .ret _ _
  | succ n ih =>
    simp only [cut]
    split
    · exact .ret _ _
    · exact .ask _ _ _ (fun a => ih (M.advance s a))
end BudgetAnalysis
