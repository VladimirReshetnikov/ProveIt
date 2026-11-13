module
public import M6.Logic.DominatedRho8
@[expose] public section

/-! Actual finite-context proof compilation, following NumericHilbert238.v
at jeff87654/busy-beaver@84049b5e753190cf328cbc2d2710791ad32ad59c.
These are proof trees, not semantic entailment. Generalization is deliberately
absent from the context rules: only closed native theorems may be imported.
This does not assert the internal arithmetic correctness of a code compiler. -/
namespace M6.PA.NativeCalculus

def identity (a : Nat) : Derivation (wim a a) :=
  .mp (Dominated.k a a)
    (.mp (Dominated.k a (wim a a)) (Dominated.s a (wim a a) a))

inductive Context (Γ : List Nat) : Nat → Type where
  | assumption {a} : a ∈ Γ → Context Γ a
  | closed {a} : Derivation a → Context Γ a
  | mp {a b} : Context Γ a → Context Γ (wim a b) → Context Γ b

def Context.cut {Γ Δ : List Nat} {a : Nat} (d : Context Γ a)
    (subst : ∀ b, b ∈ Γ → Context Δ b) : Context Δ a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => .closed p
  | .mp p q => .mp (p.cut subst) (q.cut subst)

def Context.close {Γ : List Nat} {a : Nat} (d : Context Γ a)
    (subst : ∀ b, b ∈ Γ → Derivation b) : Derivation a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => p
  | .mp p q => .mp (p.close subst) (q.close subst)

def Context.empty {a : Nat} (d : Context [] a) : Derivation a :=
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

def explosion (a : Nat) : Derivation (wim 1 a) :=
  ((Context.assumption (Γ := [1]) (by simp) : Context [1] 1).explosion a).deduction.empty

def doubleNegationElimination (a : Nat) : Derivation (wim (wn (wn a)) a) := by
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
end M6.PA.NativeCalculus

