import Std

/-!
# Boolean bounded quantification

These are ambient Lean theorems about explicit finite recursion. To obtain
object-language iPRA derivations, specialize each function argument to a fixed
primitive-recursive definition and replace finite universal invariants by `ball`.
No evaluator for all primitive-recursive programs is postulated.
-/

namespace IPRAComplexity

/-- Disjunction over the initial segment `0, ..., n-1`. -/
def bany (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bany p n || p n

/-- Conjunction over the same initial segment. -/
def ball (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => ball p n && p n

theorem bany_correct (p : Nat → Bool) (n : Nat) :
    bany p n = true ↔ ∃ i, i < n ∧ p i = true := by
  induction n with
  | zero => simp [bany]
  | succ n ih =>
    simp only [bany, Bool.or_eq_true, ih]
    constructor
    · intro h
      rcases h with ⟨i, hi, hp⟩ | hp
      · exact ⟨i, by omega, hp⟩
      · exact ⟨n, by omega, hp⟩
    · rintro ⟨i, hi, hp⟩
      by_cases h : i < n
      · exact Or.inl ⟨i, h, hp⟩
      · have he : i = n := by omega
        exact Or.inr (he ▸ hp)

theorem ball_correct (p : Nat → Bool) (n : Nat) :
    ball p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [ball]
  | succ n ih =>
    simp only [ball, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases hlt : i < n
      · exact h i hlt
      · have he : i = n := by omega
        exact he ▸ hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem bany_false_iff (p : Nat → Bool) (n : Nat) :
    bany p n = false ↔ ∀ i, i < n → p i = false := by
  constructor
  · intro h i hi
    cases hp : p i with
    | false => rfl
    | true =>
      have : bany p n = true := (bany_correct p n).2 ⟨i, hi, hp⟩
      simp_all
  · intro h
    cases hb : bany p n with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hp⟩ := (bany_correct p n).1 hb
      have := h i hi
      simp_all

/-- Bounded search returns an actual witness or `none`. -/
def firstWitness (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match firstWitness p n with
    | some i => some i
    | none => if p n then some n else none

theorem firstWitness_sound (p : Nat → Bool) (n i : Nat)
    (h : firstWitness p n = some i) : i < n ∧ p i = true := by
  induction n with
  | zero => simp [firstWitness] at h
  | succ n ih =>
    cases hw : firstWitness p n with
    | some j =>
      simp [firstWitness, hw] at h
      subst j
      obtain ⟨hlt, hp⟩ := ih hw
      exact ⟨by omega, hp⟩
    | none =>
      cases hp : p n with
      | false => simp [firstWitness, hw, hp] at h
      | true =>
        simp [firstWitness, hw, hp] at h
        subst i
        exact ⟨by omega, hp⟩

theorem firstWitness_none_iff (p : Nat → Bool) (n : Nat) :
    firstWitness p n = none ↔ bany p n = false := by
  induction n with
  | zero => simp [firstWitness, bany]
  | succ n ih =>
    cases hw : firstWitness p n with
    | some i =>
      have hb : bany p n = true :=
        (bany_correct p n).2 ⟨i, firstWitness_sound p n i hw⟩
      simp [firstWitness, hw, bany, hb]
    | none =>
      have hb : bany p n = false := ih.1 hw
      cases hp : p n <;> simp [firstWitness, hw, bany, hb, hp]

theorem bany_has_witness (p : Nat → Bool) (n : Nat)
    (h : bany p n = true) : ∃ i, firstWitness p n = some i := by
  cases hw : firstWitness p n with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have := (firstWitness_none_iff p n).1 hw
    simp_all

end IPRAComplexity
