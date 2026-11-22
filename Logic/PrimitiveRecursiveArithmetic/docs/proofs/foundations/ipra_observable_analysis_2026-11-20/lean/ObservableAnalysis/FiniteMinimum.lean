import Std

/-!
# A finite witness producer for approximate quantifiers

The list `f 0, ..., f n` is nonempty.  Its minimizing index is produced by
an explicit bounded recursion.  The stability theorem is the finite
ingredient needed for approximate infimum semantics on a supplied net.
-/

namespace ObservableAnalysis

/-- Least-index tie breaking is implemented, though only optimality is used below. -/
def argminQ (f : Nat → Rat) : Nat → Nat
  | 0 => 0
  | n + 1 => if f (argminQ f n) ≤ f (n + 1) then argminQ f n else n + 1

theorem argminQ_bound (f : Nat → Rat) (n : Nat) : argminQ f n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [argminQ]
    split <;> omega

theorem argminQ_optimal (f : Nat → Rat) (n i : Nat) (hi : i ≤ n) :
    f (argminQ f n) ≤ f i := by
  induction n with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    exact Rat.le_refl
  | succ n ih =>
    simp only [argminQ]
    split
    next h =>
      by_cases hin : i ≤ n
      · exact ih hin
      · have hieq : i = n + 1 := by omega
        subst i
        exact h
    next h =>
      by_cases hin : i ≤ n
      · exact Rat.le_trans (Rat.le_of_lt (Rat.not_le.mp h)) (ih hin)
      · have hieq : i = n + 1 := by omega
        subst i
        exact Rat.le_refl

/-- Two-sided rational error relation, avoiding an additional absolute-value API. -/
def NearQ (a b epsilon : Rat) : Prop := a ≤ b + epsilon ∧ b ≤ a + epsilon

theorem finite_minimum_upper_stability (f g : Nat → Rat) (n : Nat) (epsilon : Rat)
    (h : ∀ i, i ≤ n → f i ≤ g i + epsilon) :
    f (argminQ f n) ≤ g (argminQ g n) + epsilon := by
  have hj := argminQ_bound g n
  exact Rat.le_trans (argminQ_optimal f n (argminQ g n) hj) (h _ hj)

/-- Uniform error in a finite table produces no amplification at an infimum. -/
theorem finite_minimum_stability (f g : Nat → Rat) (n : Nat) (epsilon : Rat)
    (h : ∀ i, i ≤ n → NearQ (f i) (g i) epsilon) :
    NearQ (f (argminQ f n)) (g (argminQ g n)) epsilon := by
  constructor
  · exact finite_minimum_upper_stability f g n epsilon (fun i hi => (h i hi).1)
  · exact finite_minimum_upper_stability g f n epsilon (fun i hi => (h i hi).2)

#print axioms argminQ_bound
#print axioms argminQ_optimal
#print axioms finite_minimum_stability

end ObservableAnalysis
