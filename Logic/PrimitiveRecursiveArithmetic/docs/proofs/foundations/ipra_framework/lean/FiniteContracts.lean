import Std

/-!
# Finite contracts: semantic reference lemmas

This file intentionally uses only Lean's standard library.  Its declarations
are *host-Lean* theorems.  They do not assert that arbitrary Lean predicates
are primitive recursive, or that a host proof is an iPRA derivation.

For the object-theory theorem, restrict every program to a fixed PR symbol,
reify every invariant by a bounded Boolean test, prove the defining equations,
and use `PRA.qfInd`.  `ObjectBridge.lean` records that endpoint.
-/

namespace IPRAFramework

def run {State : Type} (initial : State)
    (step : Nat → State → State) : Nat → State
  | 0 => initial
  | n + 1 => step n (run initial step n)

theorem run_invariant {State : Type} (initial : State)
    (step : Nat → State → State) (I : Nat → State → Prop)
    (base : I 0 initial)
    (preserved : ∀ n s, I n s → I (n + 1) (step n s)) :
    ∀ n, I n (run initial step n) := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact preserved n _ ih

theorem bounded_run_invariant {State : Type} (initial : State)
    (step : Nat → State → State) (I : Nat → State → Prop) (bound : Nat)
    (base : I 0 initial)
    (preserved : ∀ n s, n < bound → I n s → I (n + 1) (step n s)) :
    ∀ n, n ≤ bound → I n (run initial step n) := by
  intro n
  induction n with
  | zero => intro _; exact base
  | succ n ih =>
      intro hn
      apply preserved n _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn)
      exact ih (Nat.le_trans (Nat.le_succ n) hn)

theorem bounded_run_exit {State : Type} (initial : State)
    (step : Nat → State → State) (I : Nat → State → Prop) (bound : Nat)
    (base : I 0 initial)
    (preserved : ∀ n s, n < bound → I n s → I (n + 1) (step n s)) :
    I bound (run initial step bound) :=
  bounded_run_invariant initial step I bound base preserved bound (Nat.le_refl _)

/-- Search only the half-open finite interval `[0, bound)`. -/
def search (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
      match search p n with
      | some i => some i
      | none => if p n then some n else none

/-- A certificate that either all candidates fail, or the returned one is least. -/
def SearchSpec (p : Nat → Bool) (bound : Nat) : Option Nat → Prop
  | none => ∀ i, i < bound → p i = false
  | some i => i < bound ∧ p i = true ∧ ∀ j, j < i → p j = false

theorem search_spec (p : Nat → Bool) (bound : Nat) :
    SearchSpec p bound (search p bound) := by
  induction bound with
  | zero =>
      intro i hi
      exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
      cases hs : search p n with
      | none =>
          have hnone : ∀ i, i < n → p i = false := by
            simpa [hs, SearchSpec] using ih
          cases hp : p n with
          | false =>
              simp only [search, hs, hp, Bool.false_eq_true, if_false, SearchSpec]
              intro i hi
              have hi' : i ≤ n := Nat.le_of_lt_succ hi
              rcases Nat.lt_or_eq_of_le hi' with hlt | heq
              · exact hnone i hlt
              · simpa [heq] using hp
          | true =>
              have hsuc : search p (n + 1) = some n := by simp [search, hs, hp]
              rw [hsuc]
              exact ⟨Nat.lt_succ_self n, hp, hnone⟩
      | some i =>
          have hi : i < n ∧ p i = true ∧ ∀ j, j < i → p j = false := by
            simpa [hs, SearchSpec] using ih
          simp only [search, hs, SearchSpec]
          exact ⟨Nat.lt_trans hi.1 (Nat.lt_succ_self n), hi.2⟩

theorem search_of_witness (p : Nat → Bool) (bound : Nat)
    (witness : ∃ i, i < bound ∧ p i = true) :
    ∃ i, search p bound = some i ∧
      i < bound ∧ p i = true ∧ ∀ j, j < i → p j = false := by
  have h := search_spec p bound
  cases hs : search p bound with
  | none =>
      have hnone : ∀ i, i < bound → p i = false := by
        simpa [hs, SearchSpec] using h
      obtain ⟨i, hi, hpi⟩ := witness
      have hbad : (true : Bool) = false := hpi.symm.trans (hnone i hi)
      cases hbad
  | some i =>
      refine ⟨i, rfl, ?_⟩
      simpa [hs, SearchSpec] using h

/-- Search observes only the supplied finite prefix, including adaptive stopping. -/
theorem search_congr (p q : Nat → Bool) (bound : Nat)
    (agree : ∀ i, i < bound → p i = q i) :
    search p bound = search q bound := by
  induction bound with
  | zero => rfl
  | succ n ih =>
      have hpq : search p n = search q n := ih
        (fun i hi => agree i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      simp only [search, hpq, agree n (Nat.lt_succ_self n)]

/-- Positive producer contract: checking alone never supplies this field. -/
structure Producer (Input Output : Type) (pre : Input → Prop)
    (post : Input → Output → Prop) where
  produce : Input → Output
  correct : ∀ x, pre x → post x (produce x)

/-- Composition explicitly uses the second producer's precondition. -/
def Producer.compose {A B C : Type} {pre : A → Prop}
    {middle : A → B → Prop} {post : A → C → Prop}
    (first : Producer A B pre middle)
    (next : A → B → C)
    (next_correct : ∀ x y, pre x → middle x y → post x (next x y)) :
    Producer A C pre post where
  produce x := next x (first.produce x)
  correct x hx := next_correct x (first.produce x) hx (first.correct x hx)

end IPRAFramework
