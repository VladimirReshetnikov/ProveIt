import ConciseIPRA.PR
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image

/-! Imported from the packet `foundations/ipra_finite_observations_2026-11-20`, `lean/Closure.lean`: the namespace is placed under `LeanProofs.IPRA.Foundations.ObservationCut` and any `#print axioms` lines are dropped. -/

/-! Finite positive rules. Empty bodies encode seeds. All rules may refer to all
heads, including their own. The tables and saturation are executable. -/
namespace LeanProofs.IPRA.Foundations.ObservationCut.FiniteClosure

structure System (n k : Nat) where
  head : Fin k → Fin n
  body : Fin k → Finset (Fin n)

variable {n k : Nat} (s : System n k)

def System.step (X : Finset (Fin n)) : Finset (Fin n) :=
  X ∪ (Finset.univ.filter (fun i => s.body i ⊆ X)).image s.head

def System.layer (s : System n k) : Nat → Finset (Fin n)
  | 0 => ∅
  | d + 1 => s.step (s.layer d)

theorem System.mem_step {a : Fin n} {X : Finset (Fin n)} :
    a ∈ s.step X ↔ a ∈ X ∨ ∃ i, s.body i ⊆ X ∧ s.head i = a := by
  simp [System.step]

theorem System.grows (X : Finset (Fin n)) : X ⊆ s.step X :=
  fun _ h => s.mem_step.mpr (Or.inl h)

def System.Closed (C : Finset (Fin n)) : Prop :=
  ∀ i, s.body i ⊆ C → s.head i ∈ C

theorem System.layer_subset {C : Finset (Fin n)} (hC : s.Closed C) :
    ∀ d, s.layer d ⊆ C := by
  intro d
  induction d with
  | zero => simp [System.layer]
  | succ d ih =>
    intro a ha
    rcases s.mem_step.mp ha with h | ⟨i, hi, rfl⟩
    · exact ih h
    · exact hC i (hi.trans ih)

theorem System.stationary_or_card (d : Nat) :
    s.step (s.layer d) = s.layer d ∨ d ≤ (s.layer d).card := by
  induction d with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ d ih =>
    rcases ih with stop | count
    · left
      change s.step (s.step (s.layer d)) = s.step (s.layer d)
      exact congrArg s.step stop
    · by_cases eqn : s.step (s.layer d) = s.layer d
      · left
        exact congrArg s.step eqn
      · right
        have strict : s.layer d ⊂ s.step (s.layer d) :=
          (s.grows _).ssubset_of_ne (Ne.symm eqn)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt count (Finset.card_lt_card strict))

theorem System.stationary : s.step (s.layer n) = s.layer n := by
  rcases s.stationary_or_card n with stop | count
  · exact stop
  · have whole : s.layer n = Finset.univ :=
      (Finset.subset_iff_eq_of_card_le (by simpa using count)).mp (Finset.subset_univ _)
    rw [whole]
    exact Finset.Subset.antisymm (Finset.subset_univ _) (s.grows _)

theorem System.least_closed : s.Closed (s.layer n) := by
  intro i hi
  rw [← s.stationary]
  exact s.mem_step.mpr (Or.inr ⟨i, hi, rfl⟩)

/-- A complement witness exists precisely for atoms outside the generated set. -/
theorem System.cut_iff (a : Fin n) :
    a ∉ s.layer n ↔ ∃ C, s.Closed C ∧ a ∉ C := by
  constructor
  · intro ha
    exact ⟨s.layer n, s.least_closed, ha⟩
  · rintro ⟨C, hC, ha⟩ h
    exact ha (s.layer_subset hC n h)

open LeanProofs.ConciseIPRA
open scoped LeanProofs.ConciseIPRA

/-- On any fixed numerical presentation, membership compiles to an actual
ordinary iPRA derivation, given derivations implementing the local rules. -/
theorem System.replay {v : Nat} (Γ : List (Fm PTm v)) (A : Fin n → Fm PTm v)
    (localProof : ∀ i, (∀ a ∈ s.body i, Γ ⊢[PRAAx] A a) → (Γ ⊢[PRAAx] A (s.head i))) :
    ∀ d a, a ∈ s.layer d → (Γ ⊢[PRAAx] A a) := by
  intro d
  induction d with
  | zero => simp [System.layer]
  | succ d ih =>
    intro a ha
    rcases s.mem_step.mp ha with h | ⟨i, hi, rfl⟩
    · exact ih a h
    · exact localProof i fun b hb => ih b (hi hb)

/-- A finite decision with distinct proof-theoretic meanings on its two sides. -/
theorem System.diagnose {v : Nat} (Γ : List (Fm PTm v)) (A : Fin n → Fm PTm v)
    (localProof : ∀ i, (∀ a ∈ s.body i, Γ ⊢[PRAAx] A a) → (Γ ⊢[PRAAx] A (s.head i)))
    (a : Fin n) : (Γ ⊢[PRAAx] A a) ∨ ∃ C, s.Closed C ∧ a ∉ C := by
  by_cases ha : a ∈ s.layer n
  · exact Or.inl (s.replay Γ A localProof n a ha)
  · exact Or.inr ((s.cut_iff a).mp ha)

end LeanProofs.IPRA.Foundations.ObservationCut.FiniteClosure
