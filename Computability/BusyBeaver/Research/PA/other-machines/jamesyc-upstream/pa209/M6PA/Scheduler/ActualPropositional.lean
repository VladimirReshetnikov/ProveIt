module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualDominated
@[expose] public section
open M6.Arithmetic.PA

/-! Reinstantiated in the NEW actual-only Proof datatype; no historical proof import.
Actual finite-context proof compilation, following NumericHilbert238.v
at jeff87654/busy-beaver@84049b5e753190cf328cbc2d2710791ad32ad59c.
These are proof trees, not semantic entailment. Generalization is deliberately
absent from the context rules: only closed native theorems may be imported.
This does not assert the internal arithmetic correctness of a code compiler. -/
namespace M6.PA.NativeCalculus.ActualCore

def identity (a : Nat) : Proof (wim a a) :=
  .mp (Dominated.k a a)
    (.mp (Dominated.k a (wim a a)) (Dominated.s a (wim a a) a))

inductive Context (Γ : List Nat) : Nat → Type where
  | assumption {a} : a ∈ Γ → Context Γ a
  | closed {a} : Proof a → Context Γ a
  | mp {a b} : Context Γ a → Context Γ (wim a b) → Context Γ b

def Context.cut {Γ Δ : List Nat} {a : Nat} (d : Context Γ a)
    (subst : ∀ b, b ∈ Γ → Context Δ b) : Context Δ a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => .closed p
  | .mp p q => .mp (p.cut subst) (q.cut subst)

def Context.close {Γ : List Nat} {a : Nat} (d : Context Γ a)
    (subst : ∀ b, b ∈ Γ → Proof b) : Proof a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => p
  | .mp p q => .mp (p.close subst) (q.close subst)

def Context.empty {a : Nat} (d : Context [] a) : Proof a :=
  d.close (fun _ h => False.elim (List.not_mem_nil h))

def Context.lift {Γ : List Nat} {a : Nat} (d : Context Γ a) (h : Nat) :
    Context Γ (wim h a) := .mp d (.closed (Dominated.k a h))

def Context.deduction {Γ : List Nat} {h a : Nat} (d : Context (h :: Γ) a) :
    Context Γ (wim h a) :=
  match d with
  | .assumption ha => by
    by_cases e : a = h
    · subst a
      exact .closed (identity h)
    · exact (Context.assumption ((List.mem_cons.mp ha).resolve_left e)).lift h
  | .closed p => (Context.closed p).lift h
  | .mp (a := b) p q => .mp p.deduction (.mp q.deduction (.closed (Dominated.s h b a)))

def Context.explosion {Γ : List Nat} (a : Nat) (d : Context Γ 1) : Context Γ a :=
  .mp (.mp d (.closed (Dominated.k 1 (wal 0 (wn (wal 0 a)))))) (.closed (.r6 0 a))

def explosion (a : Nat) : Proof (wim 1 a) :=
  ((Context.assumption (Γ := [1]) (by simp) : Context [1] 1).explosion a).deduction.empty

def doubleNegationElimination (a : Nat) : Proof (wim (wn (wn a)) a) := by
  let p : Context [wn a, wn (wn a)] (wn a) := .assumption (by simp)
  let q : Context [wn a, wn (wn a)] (wn (wn a)) := .assumption (by simp)
  let contradiction : Context [wn a, wn (wn a)] 1 := .mp p q
  let conditional : Context [wn (wn a)] (wim (wn a) a) :=
    (contradiction.explosion a).deduction
  exact (Context.mp conditional (.closed (Dominated.peirce a 1))).deduction.empty

#print axioms identity
#print axioms Context.deduction
#print axioms explosion
#print axioms doubleNegationElimination
end M6.PA.NativeCalculus.ActualCore

namespace M6.PA.NativeCalculus.ActualCore

def Context.up {Γ : List Nat} {a : Nat} (p : Context Γ a) (h : Nat) :
    Context (h :: Γ) a := p.cut (fun _ hb => .assumption (List.mem_cons_of_mem h hb))

def Context.dne {Γ : List Nat} {a : Nat} (p : Context Γ (wn (wn a))) : Context Γ a :=
  .mp p (.closed (doubleNegationElimination a))

def Context.andIntro {Γ : List Nat} {a b : Nat} (p : Context Γ a) (q : Context Γ b) :
    Context Γ (wa a b) :=
  (Context.mp (q.up (wim a (wn b)))
    (.mp (p.up (wim a (wn b))) (.assumption (by simp [wn])))).deduction

def Context.andLeft {Γ : List Nat} {a b : Nat} (p : Context Γ (wa a b)) : Context Γ a := by
  let ha : Context (a :: wn a :: Γ) a := .assumption (by simp)
  let hn : Context (a :: wn a :: Γ) (wn a) := .assumption (by simp)
  let arrow : Context (wn a :: Γ) (wim a (wn b)) :=
    ((Context.mp ha hn).explosion (wn b)).deduction
  exact (Context.mp arrow (p.up (wn a))).deduction.dne

def Context.andRight {Γ : List Nat} {a b : Nat} (p : Context Γ (wa a b)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  exact (Context.mp (hn.lift a) (p.up (wn b))).deduction.dne

def contraposition (a b : Nat) : Proof (wim (wim a b) (wim (wn b) (wn a))) := by
  let pa : Context [a, wn b, wim a b] a := .assumption (by simp)
  let pab : Context [a, wn b, wim a b] (wim a b) := .assumption (by simp)
  let pnb : Context [a, wn b, wim a b] (wn b) := .assumption (by simp)
  exact (Context.mp (.mp pa pab) pnb).deduction.deduction.deduction.empty

def contrapose {a b : Nat} (p : Proof (wim a b)) : Proof (wim (wn b) (wn a)) :=
  .mp p (contraposition a b)

def implicationCompose {a b c : Nat} (p : Proof (wim a b))
    (q : Proof (wim b c)) : Proof (wim a c) :=
  .mp q (.mp p (Dominated.composition a b c))

def Context.forallMP {Γ : List Nat} (x : Nat) {a b : Nat}
    (p : Context Γ (wal x a)) (q : Context Γ (wal x (wim a b))) : Context Γ (wal x b) :=
  .mp p (.mp q (.closed (.r2 x a b)))

/-- GEN under hypotheses requires actual finite vacuity proofs for every
assumption; a free-variable semantic predicate is not substituted for them. -/
def Context.generalize {Γ : List Nat} {a : Nat} (p : Context Γ a) (x : Nat)
    (vacuity : ∀ h, h ∈ Γ → Proof (wim h (wal x h))) : Context Γ (wal x a) :=
  match p with
  | .assumption h => .mp (.assumption h) (.closed (vacuity _ h))
  | .closed d => .closed (.all x d)
  | .mp p q => (p.generalize x vacuity).forallMP x (q.generalize x vacuity)

end M6.PA.NativeCalculus.ActualCore

