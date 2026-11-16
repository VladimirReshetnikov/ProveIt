import Std
import Lean.Elab.Tactic.Omega

/-!
# Finite observations: executable core

These are ambient Lean theorems, not object-theory iPRA derivations.
The manuscript gives the quantifier-free invariants for their arithmetization.
The function parameters must be fixed PR definitions for that interpretation.
-/

namespace IPRAEmbedding

/-- A bounded scan, retaining the first successful natural number. -/
def firstHit (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if p (firstHit p n) then firstHit p n else n + 1

theorem firstHit_le (p : Nat → Bool) (n : Nat) : firstHit p n ≤ n := by
  induction n with
  | zero => simp [firstHit]
  | succ n ih =>
    simp only [firstHit]
    split <;> omega

theorem firstHit_complete (p : Nat → Bool) (n j : Nat)
    (hj : j ≤ n) (hp : p j = true) : p (firstHit p n) = true := by
  induction n with
  | zero =>
    have h : j = 0 := by omega
    subst j
    exact hp
  | succ n ih =>
    simp only [firstHit]
    split
    · assumption
    · by_cases h : j ≤ n
      · have hfound := ih h
        contradiction
      · have hlast : j = n + 1 := by omega
        simpa [hlast] using hp

/-- Failure of the bounded scan certifies failure at every inspected index. -/
theorem firstHit_failure (p : Nat → Bool) (n : Nat)
    (h : p (firstHit p n) = false) :
    ∀ j, j ≤ n → p j = false := by
  intro j hj
  cases hp : p j with
  | false => rfl
  | true =>
    have ht := firstHit_complete p n j hj hp
    simp [h] at ht

/-- If every preceding test fails, a natural-valued energy drops by one per step. -/
theorem energy_prefix_bound (p : Nat → Bool) (E : Nat → Nat) (B : Nat)
    (h0 : E 0 ≤ B)
    (hstep : ∀ i, i ≤ B → p i = false → E (i + 1) + 1 ≤ E i)
    (hall : ∀ i, i ≤ B → p i = false) :
    ∀ i, i ≤ B + 1 → E i + i ≤ B := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ i ih =>
    intro hi
    have hiB : i ≤ B := by omega
    have hprev := ih (by omega)
    have hdrop := hstep i hiB (hall i hiB)
    omega

/-- An explicit bounded witness from a decreasing natural-valued energy. -/
theorem energy_firstHit (p : Nat → Bool) (E : Nat → Nat) (B : Nat)
    (h0 : E 0 ≤ B)
    (hstep : ∀ i, i ≤ B → p i = false → E (i + 1) + 1 ≤ E i) :
    p (firstHit p B) = true := by
  cases h : p (firstHit p B) with
  | true => rfl
  | false =>
    have hall := firstHit_failure p B h
    have hbound := energy_prefix_bound p E B h0 hstep hall (B + 1) (by omega)
    omega

/-- Disjoint closed test windows [endpoint i, endpoint i + g(endpoint i)]. -/
def endpoint (g : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | i + 1 => endpoint g start i + g (endpoint g start i) + 1

theorem endpoint_step (g : Nat → Nat) (start i : Nat) :
    endpoint g start i < endpoint g start (i + 1) := by
  simp only [endpoint]
  omega

theorem endpoint_mono (g : Nat → Nat) (start i j : Nat) (h : i ≤ j) :
    endpoint g start i ≤ endpoint g start j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i ≤ j
    · have hprev := ih hij
      have hstep := endpoint_step g start j
      omega
    · have heq : i = j + 1 := by omega
      subst i
      exact Nat.le_refl _

/-- Finite contracts describe only the input data inspected for one output. -/
structure FiniteContract where
  inputCheck : Nat → Nat → Bool
  outputCheck : Nat → Nat → Bool
  demand : Nat → Nat

/-- A contract's correctness is a theorem; a checker alone does not supply it. -/
def FiniteContract.Valid (C : FiniteContract) : Prop :=
  ∀ x k, C.inputCheck x (C.demand k) = true → C.outputCheck x k = true

theorem compose_contracts
    (A B C : Nat → Nat → Bool) (f g : Nat → Nat)
    (hAB : ∀ x k, A x (f k) = true → B x k = true)
    (hBC : ∀ x k, B x (g k) = true → C x k = true) :
    ∀ x k, A x (f (g k)) = true → C x k = true := by
  intro x k h
  exact hBC x k (hAB x (g k) h)

/-- A finite disjoint-block witness can be selected from any given successful index. -/
theorem select_window (good : Nat → Bool) (g : Nat → Nat)
    (start budget j : Nat) (hj : j ≤ budget) (hg : good j = true) :
    good (firstHit good budget) = true ∧
    endpoint g start (firstHit good budget) ≤ endpoint g start budget := by
  exact ⟨firstHit_complete good budget j hj hg,
    endpoint_mono g start _ _ (firstHit_le good budget)⟩

#print axioms firstHit_complete
#print axioms energy_firstHit
#print axioms compose_contracts
#print axioms select_window

end IPRAEmbedding
