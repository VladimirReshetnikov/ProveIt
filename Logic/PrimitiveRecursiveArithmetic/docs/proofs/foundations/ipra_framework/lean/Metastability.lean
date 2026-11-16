import Std

/-!
# Finite change budgets and metastable windows

Compiled semantic arithmetic lemmas, not an embedded `Prf PRAAx` derivation.
All function parameters become fixed PR symbols in the object-theory schema.
The source report gives the quantifier-free finite-prefix invariant.
-/

namespace IPRAFramework.Metastability

/-- Candidate starts. The extra step makes even zero-length windows advance. -/
def start (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => start g k + g (start g k) + 1

theorem start_step (g : Nat → Nat) (k : Nat) :
    start g k < start g (k + 1) := by
  simp only [start]
  omega

/-- A completely finite alternative, proved by decidable integer comparison. -/
theorem rise_or_drop (r : Nat → Nat) (n : Nat) :
    (∃ i, i < n ∧ r (i + 1) ≤ r i) ∨ r 0 + n ≤ r n := by
  induction n with
  | zero => exact Or.inr (by omega)
  | succ n ih =>
    cases ih with
    | inl h =>
      obtain ⟨i, hi, hd⟩ := h
      exact Or.inl ⟨i, by omega, hd⟩
    | inr hr =>
      by_cases hd : r (n + 1) ≤ r n
      · exact Or.inl ⟨n, by omega, hd⟩
      · exact Or.inr (by omega)

theorem bounded_change (r : Nat → Nat) (B : Nat)
    (bound : r (B + 1) ≤ B) :
    ∃ i, i ≤ B ∧ r (i + 1) ≤ r i := by
  cases rise_or_drop r (B + 1) with
  | inl h =>
    obtain ⟨i, hi, hd⟩ := h
    exact ⟨i, by omega, hd⟩
  | inr h => omega

/-- A bounded monotone natural sequence has an exactly constant requested window.
For rational sequences apply this to floor(s_n / epsilon).
-/
theorem constant_window (a : Nat → Nat) (g : Nat → Nat) (B : Nat)
    (mono : ∀ i j, i ≤ j → a i ≤ a j)
    (bound : a (start g (B + 1)) ≤ B) :
    ∃ k, k ≤ B ∧
      ∀ i, start g k ≤ i → i ≤ start g k + g (start g k) →
        a i = a (start g k) := by
  obtain ⟨k, hk, hd⟩ := bounded_change (fun j => a (start g j)) B bound
  refine ⟨k, hk, ?_⟩
  intro i hlo hhi
  have hlow := mono (start g k) i hlo
  have hend : i ≤ start g (k + 1) := by
    simp only [start]
    omega
  have hupp := mono i (start g (k + 1)) hend
  change a (start g (k + 1)) ≤ a (start g k) at hd
  omega

/-- Finite bounded cardinality yields an empty one of B+1 disjoint windows.
The explicit count prefix is supplied as data, allowing a PR implementation.
-/
def cumulative (hit : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cumulative hit n + if hit n then 1 else 0

theorem cumulative_mono_step (hit : Nat → Bool) (n : Nat) :
    cumulative hit n ≤ cumulative hit (n + 1) := by
  simp only [cumulative]
  split <;> omega

end IPRAFramework.Metastability

#print axioms IPRAFramework.Metastability.rise_or_drop
#print axioms IPRAFramework.Metastability.bounded_change
#print axioms IPRAFramework.Metastability.constant_window
