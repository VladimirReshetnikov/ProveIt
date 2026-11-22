import Mathlib.Tactic.Linarith

/-! The numerical estimate for extending a rational evaluator to regular names.
All hypotheses concern distances of samples. No quotient or completion is an input. -/
namespace FiniteObservation.Completion

def err : Nat → ℚ
  | 0 => 1
  | k + 1 => err k / 2

theorem err_nonneg (k : Nat) : 0 ≤ err k := by
  induction k with
  | zero => decide
  | succ k ih =>
    change 0 ≤ err k / 2
    linarith

theorem err_anti {a b : Nat} (h : a ≤ b) : err b ≤ err a := by
  induction h with
  | refl => exact le_rfl
  | @step n _ ih =>
    change err n / 2 ≤ _
    linarith [err_nonneg n]

structure Distance (X : Type) where
  d : X → X → ℚ
  symm : ∀ x y, d x y = d y x
  tri : ∀ x y z, d x z ≤ d x y + d y z

variable {X Y : Type}

def Close (D : Distance X) (x y : Nat → X) :=
  ∀ n m, D.d (x n) (y m) ≤ err n + err m

def service (μ : Nat → Nat) (n : Nat) := max (n+2) (μ (n+2)+1)

theorem extend_close (A : Distance X) (B : Distance Y) (μ : Nat → Nat)
    (E : X → Nat → Y) (bound : ∀ x y k i j, A.d x y ≤ err (μ k) →
      B.d (E x i) (E y j) ≤ err i + err k + err j)
    (a b : Nat → X) (ha : Close A a a) (hab : Close A a b) :
    Close B (fun n => E (a (service μ n)) (n+2))
      (fun m => E (b (service μ m)) (m+2)) := by
  intro n m
  let L := max (service μ n) (service μ m)
  let j := max (n+2) (m+2)
  have sn (t : Nat) : err (service μ t) ≤ err (μ (t+2)) / 2 :=
    err_anti (Nat.le_max_right _ _)
  have smallN : err L ≤ err (service μ n) := err_anti (Nat.le_max_left _ _)
  have smallM : err L ≤ err (service μ m) := err_anti (Nat.le_max_right _ _)
  have nx : A.d (a (service μ n)) (a L) ≤ err (μ (n+2)) := by
    linarith [ha (service μ n) L, sn n]
  have mx : A.d (a L) (b (service μ m)) ≤ err (μ (m+2)) := by
    linarith [hab L (service μ m), sn m]
  have hn := bound _ _ _ (n+2) j nx
  have hm := bound _ _ _ j (m+2) mx
  have tri := B.tri (E (a (service μ n)) (n+2)) (E (a L) j) (E (b (service μ m)) (m+2))
  have jn : err j ≤ err (n+2) := err_anti (Nat.le_max_left _ _)
  have jm : err j ≤ err (m+2) := err_anti (Nat.le_max_right _ _)
  have quarter (t : Nat) : err (t+2) = err t / 2 / 2 := rfl
  change B.d _ _ ≤ err n + err m
  linarith [quarter n, quarter m, err_nonneg n, err_nonneg m]

end FiniteObservation.Completion
