import Std.Tactic

/-! Finite back-and-forth for quantitative formulas. Table entries are integers
in units of a common positive denominator. This file proves host Lean lemmas.
The manuscript specifies specialization to fixed iPRA programs. -/
namespace ModelCase

universe u v w

def Near (eps a b : Nat) : Prop := a ≤ b + eps ∧ b ≤ a + eps

structure Net (α : Type u) where
  first : α
  rest : List α

def Net.elems (s : Net α) : List α := s.first :: s.rest

/-- Least-cost sample, breaking ties by position. -/
def best (cost : α → Nat) (first : α) : List α → α
  | [] => first
  | next :: rest =>
    let tail := best cost next rest
    if cost first ≤ cost tail then first else tail

theorem best_mem (cost : α → Nat) (first : α) (xs : List α) :
    best cost first xs ∈ first :: xs := by
  induction xs generalizing first with
  | nil => simp [best]
  | cons next xs ih =>
    simp only [best]
    split
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem first (ih next)

theorem best_le (cost : α → Nat) (first : α) (xs : List α)
    (x : α) (h : x ∈ first :: xs) : cost (best cost first xs) ≤ cost x := by
  induction xs generalizing first with
  | nil => simpa [best] using (show cost first ≤ cost x from
      (by simpa using h : x = first) ▸ Nat.le_refl _)
  | cons next xs ih =>
    simp only [best]
    split
    next cmp =>
      rcases List.mem_cons.mp h with eq | mem
      · subst x; exact Nat.le_refl _
      · exact Nat.le_trans cmp (ih next mem)
    next cmp =>
      rcases List.mem_cons.mp h with eq | mem
      · subst x; exact Nat.le_of_lt (Nat.lt_of_not_ge cmp)
      · exact ih next mem

def Net.minimum (s : Net α) (f : α → Nat) : Nat :=
  f (best f s.first s.rest)

structure Corresponds (s : Net α) (t : Net β) (R : α → β → Prop) : Prop where
  forth : ∀ a ∈ s.elems, ∃ b ∈ t.elems, R a b
  back : ∀ b ∈ t.elems, ∃ a ∈ s.elems, R a b

theorem near_minimum {s : Net α} {t : Net β} {R : α → β → Prop}
    (cover : Corresponds s t R) (f : α → Nat) (g : β → Nat)
    (h : ∀ a b, R a b → Near e (f a) (g b)) :
    Near e (s.minimum f) (t.minimum g) := by
  let a := best f s.first s.rest
  let b := best g t.first t.rest
  obtain ⟨a', ha', hab'⟩ := cover.back b (best_mem _ _ _)
  obtain ⟨b', hb', hab⟩ := cover.forth a (best_mem _ _ _)
  constructor
  · exact Nat.le_trans (best_le f s.first s.rest a' ha') (h a' b hab').1
  · exact Nat.le_trans (best_le g t.first t.rest b' hb') (h a b' hab).2

/-- Fixed connective on scaled natural entries. Nonexpansiveness in the sup
metric allows the same error through every connective. -/
structure Connective where
  run : Nat → Nat → Nat
  stable : ∀ {e a b c d}, Near e a c → Near e b d → Near e (run a b) (run c d)

def smaller : Connective where
  run := min
  stable := by intro e a b c d ⟨h₁, h₂⟩ ⟨h₃, h₄⟩; constructor <;> omega

def larger : Connective where
  run := max
  stable := by intro e a b c d ⟨h₁, h₂⟩ ⟨h₃, h₄⟩; constructor <;> omega

/-- An atom of arity n can read precisely the n indicated variables; the
leftmost variable has de Bruijn index 0. -/
inductive Formula (A : Nat → Type u) : Nat → Type u
  | atom {n} (symbol : A n) : Formula A n
  | conn {n} (op : Connective) (p q : Formula A n) : Formula A n
  | neg {n} (p : Formula A n) : Formula A n
  | infQ {n} (p : Formula A (n+1)) : Formula A n

def extend (x : α) (env : Fin n → α) : Fin (n+1) → α := Fin.cases x env

def Related (R : α → β → Prop) (env : Fin n → α) (env' : Fin n → β) : Prop :=
  ∀ i, R (env i) (env' i)

theorem extend_related {R : α → β → Prop} {env : Fin n → α} {env' : Fin n → β}
    (h : Related R env env') (hxy : R x y) :
    Related R (extend x env) (extend y env') :=
  fun i => Fin.cases hxy (fun j => h j) i

/-- S is the integer representing 1; for [0,S]-valued atoms and operations,
negation is the ordinary continuous-negation connective and sup is its inf-dual. -/
def value {A : Nat → Type u} (S : Nat) (net : Net α)
    (atomValue : ∀ {n}, A n → (Fin n → α) → Nat) :
    {n : Nat} → Formula A n → (Fin n → α) → Nat
  | _, .atom sym, env => atomValue sym env
  | _, .conn op p q, env => op.run (value S net atomValue p env) (value S net atomValue q env)
  | _, .neg p, env => S - value S net atomValue p env
  | _, .infQ p, env => net.minimum (fun x => value S net atomValue p (extend x env))

/-- Uniform in formula and independent of quantifier rank. -/
theorem transfer {A : Nat → Type u} {s : Net α} {t : Net β} {R : α → β → Prop}
    (S e : Nat) (va : ∀ {n}, A n → (Fin n → α) → Nat)
    (vb : ∀ {n}, A n → (Fin n → β) → Nat)
    (cover : Corresponds s t R)
    (atomic : ∀ {n} (p : A n) env env', Related R env env' → Near e (va p env) (vb p env'))
    {n} (p : Formula A n) (env : Fin n → α) (env' : Fin n → β)
    (h : Related R env env') : Near e (value S s va p env) (value S t vb p env') := by
  induction p with
  | atom p => exact atomic p env env' h
  | conn op p q hp hq => exact op.stable (hp env env' h) (hq env env' h)
  | neg p ih =>
    have ⟨h₁, h₂⟩ := ih env env' h
    simp only [value, Near]; constructor <;> omega
  | infQ p ih =>
    exact near_minimum cover _ _ (fun a b hab => ih _ _ (extend_related h hab))

#print axioms near_minimum
#print axioms transfer

end ModelCase
