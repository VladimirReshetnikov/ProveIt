import Std

/-!
# Finite arithmetic used by the constructive implicit function theorem

This is a **host Lean** development.  It does not claim to construct a derivation
in the object theory iPRA.  The accompanying blueprint explains that remaining
translation.  The file imports only Lean's bundled standard library.

The central estimate is division-free: natural numbers represent nonnegative
rational errors after one common positive denominator has been chosen.  A
finite half-contraction trace satisfying `2*d(i+1) <= d(i)+2*e` has the exact
weighted error budget proved below.  Neither limits nor choice occur here.
-/

namespace ConstructiveIFT

/-- A sum of the scaled local errors.  `e` is a numerator over a common
positive denominator. -/
def errorBudget (initial e : Nat) : Nat → Nat
  | 0 => initial
  | n + 1 => errorBudget initial e n + 2 ^ (n + 1) * e

theorem two_pow_succ (n : Nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  simp [Nat.pow_succ, Nat.mul_two]

/-- The exact finite geometric sum, without truncated subtraction. -/
theorem errorBudget_closed (initial e n : Nat) :
    errorBudget initial e n + 2 * e = initial + 2 ^ (n + 1) * e := by
  induction n with
  | zero => simp [errorBudget]
  | succ n ih =>
    simp only [errorBudget, two_pow_succ, Nat.add_mul] at ih ⊢
    omega

/-- A uniformly bounded one-step defect gives a finite scaled budget. -/
theorem half_contraction_budget (d : Nat → Nat) (e : Nat)
    (step : ∀ i, 2 * d (i + 1) ≤ d i + 2 * e) :
    ∀ n, 2 ^ n * d n ≤ errorBudget (d 0) e n := by
  intro n
  induction n with
  | zero => simp [errorBudget]
  | succ n ih =>
    calc
      2 ^ (n + 1) * d (n + 1)
          = 2 ^ n * (2 * d (n + 1)) := by
            simp [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ n * (d n + 2 * e) :=
            Nat.mul_le_mul_left (2 ^ n) (step n)
      _ = 2 ^ n * d n + 2 ^ (n + 1) * e := by
            simp [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc]
      _ ≤ errorBudget (d 0) e n + 2 ^ (n + 1) * e :=
            Nat.add_le_add_right ih _
      _ = errorBudget (d 0) e (n + 1) := rfl

/-- Cleared form of `d_n <= 2^(-n)*d_0 + 2e*(1-2^(-n))`.
The statement has no division, subtraction, or real numbers. -/
theorem half_contraction_closed (d : Nat → Nat) (e : Nat)
    (step : ∀ i, 2 * d (i + 1) ≤ d i + 2 * e) (n : Nat) :
    2 ^ n * d n + 2 * e ≤ d 0 + 2 ^ (n + 1) * e := by
  calc
    2 ^ n * d n + 2 * e ≤ errorBudget (d 0) e n + 2 * e :=
      Nat.add_le_add_right (half_contraction_budget d e step n) _
    _ = d 0 + 2 ^ (n + 1) * e := errorBudget_closed (d 0) e n

/-- The same proof needs hypotheses only for the actual finite trace. -/
theorem half_contraction_budget_finite (d : Nat → Nat) (e N : Nat)
    (step : ∀ i, i < N → 2 * d (i + 1) ≤ d i + 2 * e) :
    2 ^ N * d N ≤ errorBudget (d 0) e N := by
  induction N with
  | zero => simp [errorBudget]
  | succ N ih =>
    have prev : 2 ^ N * d N ≤ errorBudget (d 0) e N :=
      ih (fun i hi => step i (by omega))
    calc
      2 ^ (N + 1) * d (N + 1)
          = 2 ^ N * (2 * d (N + 1)) := by
            simp [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ N * (d N + 2 * e) :=
            Nat.mul_le_mul_left (2 ^ N) (step N (by omega))
      _ = 2 ^ N * d N + 2 ^ (N + 1) * e := by
            simp [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc]
      _ ≤ errorBudget (d 0) e N + 2 ^ (N + 1) * e :=
            Nat.add_le_add_right prev _
      _ = errorBudget (d 0) e (N + 1) := rfl

/-- A finite Boolean checker. For each fixed primitive recursive `d`, this
definition is primitive recursive. No universal interpreter is asserted. -/
def checkSteps (d : Nat → Nat) (e : Nat) : Nat → Bool
  | 0 => true
  | N + 1 => checkSteps d e N && decide (2 * d (N + 1) ≤ d N + 2 * e)

/-- This proof follows the quantifier-free induction invariant intended for
the object arithmetic: a Boolean certificate equation implies one numerical
inequality. The host Lean parameters will become fixed PR symbols there. -/
theorem checked_half_contraction_budget (d : Nat → Nat) (e N : Nat)
    (checked : checkSteps d e N = true) :
    2 ^ N * d N ≤ errorBudget (d 0) e N := by
  induction N with
  | zero => simp [errorBudget]
  | succ N ih =>
    simp only [checkSteps, Bool.and_eq_true, decide_eq_true_eq] at checked
    have prev := ih checked.1
    calc
      2 ^ (N + 1) * d (N + 1)
          = 2 ^ N * (2 * d (N + 1)) := by
            simp [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ N * (d N + 2 * e) :=
            Nat.mul_le_mul_left (2 ^ N) checked.2
      _ = 2 ^ N * d N + 2 ^ (N + 1) * e := by
            simp [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc]
      _ ≤ errorBudget (d 0) e N + 2 ^ (N + 1) * e :=
            Nat.add_le_add_right prev _
      _ = errorBudget (d 0) e (N + 1) := rfl

/-- Iteration depth used in the manuscript; `2*r <= 2^s`. -/
def steps (precision radiusExponent : Nat) : Nat :=
  precision + radiusExponent + 4

theorem steps_mono (s : Nat) {k l : Nat} (h : k ≤ l) :
    steps k s ≤ steps l s := by
  unfold steps
  omega

theorem steps_zero_margin (k s : Nat) : k + 4 ≤ steps k s := by
  unfold steps
  omega

/-- Finite iteration with a fixed evaluator.  This is not a universal
evaluator for codes of all primitive recursive functions. -/
def iterate {α : Type} (T : α → α) (start : α) : Nat → α
  | 0 => start
  | n + 1 => T (iterate T start n)

theorem iterate_add {α : Type} (T : α → α) (start : α) (m n : Nat) :
    iterate T start (m + n) = iterate T (iterate T start m) n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih => simp [iterate, ih]

/-!
## A finite Neumann identity

We make the additive laws explicit, so no analytical or algebraic axioms are
silently imported.  For a linear map A and a vector b, `powerVector` is A^n b
and `neumannVector` is b + A b + ... + A^(n-1) b.  Its exact residual identity
is the finite algebraic input to the inverse derivative construction.
-/

section Neumann

variable {V : Type} (zero : V) (add : V → V → V) (A : V → V)

def powerVector (b : V) : Nat → V
  | 0 => b
  | n + 1 => A (powerVector b n)

def neumannVector (b : V) : Nat → V
  | 0 => zero
  | n + 1 => add (A (neumannVector b n)) b

/-- `z_n + A^n b = A z_n + b`, requiring only finite additive algebra. -/
theorem neumann_residual
    (addAssoc : ∀ x y z, add (add x y) z = add x (add y z))
    (addComm : ∀ x y, add x y = add y x)
    (mapZero : A zero = zero)
    (mapAdd : ∀ x y, A (add x y) = add (A x) (A y))
    (b : V) (n : Nat) :
    add (neumannVector zero add A b n) (powerVector A b n) =
      add (A (neumannVector zero add A b n)) b := by
  induction n with
  | zero => simp [neumannVector, powerVector, mapZero]
  | succ n ih =>
    simp only [neumannVector, powerVector]
    calc
      add (add (A (neumannVector zero add A b n)) b)
          (A (powerVector A b n))
          = add (A (neumannVector zero add A b n))
              (add b (A (powerVector A b n))) := addAssoc _ _ _
      _ = add (A (neumannVector zero add A b n))
              (add (A (powerVector A b n)) b) := by
            rw [addComm b (A (powerVector A b n))]
      _ = add (add (A (neumannVector zero add A b n))
              (A (powerVector A b n))) b := (addAssoc _ _ _).symm
      _ = add (A (add (neumannVector zero add A b n)
              (powerVector A b n))) b := by rw [mapAdd]
      _ = add (A (add (A (neumannVector zero add A b n)) b)) b := by rw [ih]

end Neumann

-- Kernel dependency reports are retained in build.log.
#print axioms half_contraction_budget_finite
#print axioms half_contraction_closed
#print axioms checked_half_contraction_budget
#print axioms iterate_add
#print axioms neumann_residual

end ConstructiveIFT
