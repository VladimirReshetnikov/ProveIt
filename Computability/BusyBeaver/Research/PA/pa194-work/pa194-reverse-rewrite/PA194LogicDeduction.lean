import PA194LogicImplicationBasis

/-! Actual finite-context proof compilation, following NumericHilbert238.v
at jeff87654/busy-beaver@84049b5e753190cf328cbc2d2710791ad32ad59c.
These are proof trees, not semantic entailment. Generalization is deliberately
absent from the context rules: only closed native theorems may be imported.
This does not assert the internal arithmetic correctness of a code compiler. -/
namespace PA194Logic

/-- Distribution is derived from the actual antecedent-reversed sixth head. -/
def r2 (d a h : Nat) :
    Derivation (wim (wal d (wim a h)) (wim (wal d a) (wal d h))) :=
  .mp (.h6 d a h) (Dominated.exchange (wal d a) (wal d (wim a h)) (wal d h))

def r4 (d a h : Nat) : Derivation (wim (wal d (wal a h)) (wal a (wal d h))) :=
  .h2 d a h

def r6 (d h : Nat) : Derivation (wim (wex d (wal d h)) h) := .h1 d h

/-- Witness equality is deliberately mirrored: E(h,d), not E(d,h). -/
def r1 (d h : Nat) : Derivation (wex d (weq h d)) := .h5 d h

def memRight (a b c : Nat) : Derivation (wim (weq a b) (wim (wel c a) (wel c b))) :=
  .h4 a b c

def memLeft (a b c : Nat) : Derivation (wim (weq a b) (wim (wel a c) (wel b c))) :=
  .mp (.h3 a c b) (Dominated.exchange (wel a c) (weq a b) (wel b c))

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
  .mp (.mp d (.closed (Dominated.k 1 (wal 0 (wn (wal 0 a)))))) (.closed (.h1 0 a))

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
end PA194Logic

