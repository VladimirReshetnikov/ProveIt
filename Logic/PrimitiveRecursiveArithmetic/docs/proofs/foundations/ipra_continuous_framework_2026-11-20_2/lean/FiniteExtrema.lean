import Std

/-!
# Finite extrema of scaled nonnegative scores

Checked semantic kernel.  This file proves Lean propositions about natural
scores; it is NOT an object-theory `Prf PRAAx` derivation.  A score `a` may
represent a nonnegative rational `a / D` at one fixed positive denominator.
All extrema below are over the NONEMPTY range `0, ..., n`.
-/

namespace QuantitativeIPRA

/-- Two-sided additive error, avoiding truncated natural subtraction. -/
def Close (e a b : Nat) : Prop := a ≤ b + e ∧ b ≤ a + e

theorem close_refl (e a : Nat) : Close e a a := by
  constructor <;> omega

theorem close_symm {e a b : Nat} (h : Close e a b) : Close e b a :=
  ⟨h.2, h.1⟩

theorem close_mono {e e' a b : Nat} (h : Close e a b) (he : e ≤ e') :
    Close e' a b := by
  rcases h with ⟨h₁, h₂⟩
  constructor <;> omega

theorem close_trans {e d a b c : Nat} (h : Close e a b) (k : Close d b c) :
    Close (e + d) a c := by
  rcases h with ⟨h₁, h₂⟩
  rcases k with ⟨k₁, k₂⟩
  constructor <;> omega

theorem close_max {e a b c d : Nat} (h : Close e a b) (k : Close e c d) :
    Close e (max a c) (max b d) := by
  rcases h with ⟨h₁, h₂⟩
  rcases k with ⟨k₁, k₂⟩
  constructor <;> omega

theorem close_min {e a b c d : Nat} (h : Close e a b) (k : Close e c d) :
    Close e (min a c) (min b d) := by
  rcases h with ⟨h₁, h₂⟩
  rcases k with ⟨k₁, k₂⟩
  constructor <;> omega

/-- Clipping or taking a bounded complement does not enlarge error. -/
theorem close_complement {e a b : Nat} (B : Nat) (h : Close e a b) :
    Close e (B - a) (B - b) := by
  rcases h with ⟨h₁, h₂⟩
  constructor <;> omega

theorem close_truncated_difference {e d a b c f : Nat}
    (h : Close e a b) (k : Close d c f) :
    Close (e + d) (a - c) (b - f) := by
  rcases h with ⟨h₁, h₂⟩
  rcases k with ⟨k₁, k₂⟩
  constructor <;> omega

def maxScore (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (maxScore f n) (f (n + 1))

def minScore (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => min (minScore f n) (f (n + 1))

theorem score_le_max (f : Nat → Nat) (n i : Nat) (hi : i ≤ n) :
    f i ≤ maxScore f n := by
  induction n with
  | zero =>
    have : i = 0 := by omega
    simp [this, maxScore]
  | succ n ih =>
    by_cases h : i ≤ n
    · have h' := ih h
      have m := Nat.le_max_left (maxScore f n) (f (n + 1))
      exact Nat.le_trans h' m
    · have : i = n + 1 := by omega
      simpa [this, maxScore] using Nat.le_max_right (maxScore f n) (f (n + 1))

theorem min_le_score (f : Nat → Nat) (n i : Nat) (hi : i ≤ n) :
    minScore f n ≤ f i := by
  induction n with
  | zero =>
    have : i = 0 := by omega
    simp [this, minScore]
  | succ n ih =>
    by_cases h : i ≤ n
    · have h' := ih h
      have m := Nat.min_le_left (minScore f n) (f (n + 1))
      exact Nat.le_trans m h'
    · have : i = n + 1 := by omega
      simpa [this, minScore] using Nat.min_le_right (minScore f n) (f (n + 1))

theorem max_le (f : Nat → Nat) (n B : Nat) (h : ∀ i, i ≤ n → f i ≤ B) :
    maxScore f n ≤ B := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ n ih =>
    have h' : maxScore f n ≤ B := ih (fun i hi => h i (by omega))
    have h'' : f (n + 1) ≤ B := h _ (Nat.le_refl _)
    exact Nat.max_le.mpr ⟨h', h''⟩

theorem le_min (f : Nat → Nat) (n B : Nat) (h : ∀ i, i ≤ n → B ≤ f i) :
    B ≤ minScore f n := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ n ih =>
    have h' : B ≤ minScore f n := ih (fun i hi => h i (by omega))
    have h'' : B ≤ f (n + 1) := h _ (Nat.le_refl _)
    exact Nat.le_min.mpr ⟨h', h''⟩

/-- Pointwise error stays `e`, irrespective of the number of samples. -/
theorem max_stability (f g : Nat → Nat) (n e : Nat)
    (h : ∀ i, i ≤ n → Close e (f i) (g i)) :
    Close e (maxScore f n) (maxScore g n) := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ n ih =>
    exact close_max (ih (fun i hi => h i (by omega))) (h _ (Nat.le_refl _))

theorem min_stability (f g : Nat → Nat) (n e : Nat)
    (h : ∀ i, i ≤ n → Close e (f i) (g i)) :
    Close e (minScore f n) (minScore g n) := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ n ih =>
    exact close_min (ih (fun i hi => h i (by omega))) (h _ (Nat.le_refl _))

/-- The earlier index is retained on ties. -/
def argmin (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if f (n + 1) < f (argmin f n) then n + 1 else argmin f n

def argmax (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if f (argmax f n) < f (n + 1) then n + 1 else argmax f n

theorem argmin_le (f : Nat → Nat) (n : Nat) : argmin f n ≤ n := by
  induction n with
  | zero => simp [argmin]
  | succ n ih => simp only [argmin]; split <;> omega

theorem argmax_le (f : Nat → Nat) (n : Nat) : argmax f n ≤ n := by
  induction n with
  | zero => simp [argmax]
  | succ n ih => simp only [argmax]; split <;> omega

theorem argmin_attains (f : Nat → Nat) (n : Nat) :
    f (argmin f n) = minScore f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [argmin, minScore]
    split
    · rename_i h
      omega
    · rename_i h
      omega

theorem argmax_attains (f : Nat → Nat) (n : Nat) :
    f (argmax f n) = maxScore f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [argmax, maxScore]
    split
    · rename_i h
      omega
    · rename_i h
      omega

/-- The selected minimum index is the first minimizer in the range. -/
theorem argmin_le_of_attains (f : Nat → Nat) (n i : Nat)
    (hi : i ≤ n) (hval : f i = minScore f n) : argmin f n ≤ i := by
  induction n with
  | zero => simp [argmin]
  | succ n ih =>
    simp only [argmin]
    split
    · rename_i h
      have old := argmin_attains f n
      have : ¬ i ≤ n := by
        intro hin
        have hmin := min_le_score f n i hin
        simp only [minScore] at hval
        omega
      omega
    · rename_i h
      by_cases hin : i ≤ n
      · have old := argmin_attains f n
        have hv : f i = minScore f n := by
          simp only [minScore] at hval
          omega
        exact ih hin hv
      · have hh := argmin_le f n
        omega

/-- A correspondence between two nonempty finite index sets.  Totality is
    supplied in both directions and need not be a bijection. -/
structure TotalCorrespondence (R : Nat → Nat → Prop) (n m : Nat) : Prop where
  left : ∀ i, i ≤ n → ∃ j, j ≤ m ∧ R i j
  right : ∀ j, j ≤ m → ∃ i, i ≤ n ∧ R i j

theorem min_correspondence (f g : Nat → Nat) (n m e : Nat)
    (R : Nat → Nat → Prop) (ht : TotalCorrespondence R n m)
    (h : ∀ i, i ≤ n → ∀ j, j ≤ m → R i j → Close e (f i) (g j)) :
    Close e (minScore f n) (minScore g m) := by
  constructor
  · rcases ht.right (argmin g m) (argmin_le g m) with ⟨i, hi, hR⟩
    have h₁ := (h i hi _ (argmin_le g m) hR).1
    have h₂ := min_le_score f n i hi
    rw [argmin_attains g m] at h₁
    omega
  · rcases ht.left (argmin f n) (argmin_le f n) with ⟨j, hj, hR⟩
    have h₁ := (h _ (argmin_le f n) j hj hR).2
    have h₂ := min_le_score g m j hj
    rw [argmin_attains f n] at h₁
    omega

theorem max_correspondence (f g : Nat → Nat) (n m e : Nat)
    (R : Nat → Nat → Prop) (ht : TotalCorrespondence R n m)
    (h : ∀ i, i ≤ n → ∀ j, j ≤ m → R i j → Close e (f i) (g j)) :
    Close e (maxScore f n) (maxScore g m) := by
  constructor
  · rcases ht.left (argmax f n) (argmax_le f n) with ⟨j, hj, hR⟩
    have h₁ := (h _ (argmax_le f n) j hj hR).1
    have h₂ := score_le_max g m j hj
    rw [argmax_attains f n] at h₁
    omega
  · rcases ht.right (argmax g m) (argmax_le g m) with ⟨i, hi, hR⟩
    have h₁ := (h i hi _ (argmax_le g m) hR).2
    have h₂ := score_le_max f n i hi
    rw [argmax_attains g m] at h₁
    omega

end QuantitativeIPRA
