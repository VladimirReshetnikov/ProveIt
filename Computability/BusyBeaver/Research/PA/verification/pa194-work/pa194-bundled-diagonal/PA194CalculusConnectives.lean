import PA194CalculusTruth
set_option autoImplicit false
namespace PA194CalculusConnectives
open PA194DerivationCompiler PA194CalculusTruth PA196.Commands.Code

def neg (a : Nat) := I a 1

def peirce (a b : Nat) : Derivation (I (I (I a b) a) a) :=
  M6.Logic.RestrictedImplication.peirce rules a b

inductive Context (Γ : List Nat) : Nat → Type where
  | assumption {a} : a ∈ Γ → Context Γ a
  | closed {a} : Derivation a → Context Γ a
  | mp {a b} : Context Γ a → Context Γ (I a b) → Context Γ b

def Context.close {Γ : List Nat} {a : Nat} (d : Context Γ a)
    (subst : ∀ b, b ∈ Γ → Derivation b) : Derivation a :=
  match d with
  | .assumption h => subst _ h
  | .closed p => p
  | .mp p q => .mp (p.close subst) (q.close subst)

def Context.empty {a : Nat} (d : Context [] a) : Derivation a :=
  d.close (fun _ h => False.elim (List.not_mem_nil h))

def Context.lift {Γ : List Nat} {a : Nat} (d : Context Γ a) (h : Nat) : Context Γ (I h a) :=
  .mp d (.closed (k a h))

def Context.deduction {Γ : List Nat} {h a : Nat} (d : Context (h :: Γ) a) : Context Γ (I h a) :=
  match d with
  | .assumption ha => by
    by_cases e : a = h
    · subst a
      exact .closed (identity h)
    · exact (Context.assumption ((List.mem_cons.mp ha).resolve_left e)).lift h
  | .closed p => (Context.closed p).lift h
  | .mp (a := b) p q => .mp p.deduction (.mp q.deduction (.closed (s h b a)))

def Context.explosion {Γ : List Nat} (a : Nat) (d : Context Γ 1) : Context Γ a :=
  .mp (.mp d (.closed (k 1 (U 0 (neg (U 0 a)))))) (.closed (.h1 0 a))

def doubleNegationElimination (a : Nat) : Derivation (I (neg (neg a)) a) := by
  let p : Context [neg a,neg (neg a)] (neg a) := .assumption (by simp)
  let q : Context [neg a,neg (neg a)] (neg (neg a)) := .assumption (by simp)
  let contradiction : Context [neg a,neg (neg a)] 1 := .mp p q
  let conditional : Context [neg (neg a)] (I (neg a) a) :=
    (contradiction.explosion a).deduction
  exact (Context.mp conditional (.closed (peirce a 1))).deduction.empty

#print axioms doubleNegationElimination
end PA194CalculusConnectives
