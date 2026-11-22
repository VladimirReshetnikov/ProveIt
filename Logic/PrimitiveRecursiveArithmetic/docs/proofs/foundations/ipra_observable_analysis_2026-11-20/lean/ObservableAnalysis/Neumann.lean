import Std

/-!
# Finite Neumann polynomials and a perturbed contraction

These are algebraic metatheorems over an explicitly supplied (possibly
noncommutative) ring.  For an iPRA application the ring operations, finite
iteration and equality certificate must first be realized by fixed primitive
recursive recipes.  This file does not assert a proof compiler into iPRA.
-/

namespace ObservableAnalysis

open Lean.Grind

universe u

variable {A : Type u} [Ring A]

private theorem mul_sub (a b c : A) : a * (b - c) = a * b - a * c := by
  simp only [Ring.sub_eq_add_neg, Semiring.left_distrib, Ring.mul_neg]

private theorem sub_mul (a b c : A) : (a - b) * c = a * c - b * c := by
  simp only [Ring.sub_eq_add_neg, Semiring.right_distrib, Ring.neg_mul]

private theorem subtract_telescope (a b c : A) : (a - b) + (b - c) = a - c := by
  simp only [Ring.sub_eq_add_neg, ← Semiring.add_assoc]
  rw [Semiring.add_assoc a (-b) b, Ring.neg_add_cancel, Semiring.add_zero]

/-- The finite polynomial `1 + R + ... + R^(n-1)`, with the empty sum zero. -/
def geometricSum (R : A) : Nat → A
  | 0 => 0
  | n + 1 => geometricSum R n + R ^ n

theorem pow_commutes (R : A) (n : Nat) : R * R ^ n = R ^ n * R := by
  induction n with
  | zero => simp only [Semiring.pow_zero, Semiring.mul_one, Semiring.one_mul]
  | succ n ih =>
    simp only [Semiring.pow_succ]
    rw [← Semiring.mul_assoc, ih]

/-- Exact left inverse residual; no convergence hypothesis is used. -/
theorem geometric_left (R : A) (n : Nat) :
    (1 - R) * geometricSum R n = 1 - R ^ n := by
  induction n with
  | zero =>
    simp only [geometricSum, Semiring.pow_zero, Semiring.mul_zero]
    exact (AddCommGroup.sub_self 1).symm
  | succ n ih =>
    simp only [geometricSum, Semiring.pow_succ]
    have hc := pow_commutes R n
    rw [Semiring.left_distrib, ih, sub_mul, Semiring.one_mul, hc]
    exact subtract_telescope _ _ _

/-- Exact right inverse residual; valid without commutativity of the ring. -/
theorem geometric_right (R : A) (n : Nat) :
    geometricSum R n * (1 - R) = 1 - R ^ n := by
  induction n with
  | zero =>
    simp only [geometricSum, Semiring.pow_zero, Semiring.zero_mul]
    exact (AddCommGroup.sub_self 1).symm
  | succ n ih =>
    simp only [geometricSum, Semiring.pow_succ]
    rw [Semiring.right_distrib, ih, mul_sub, Semiring.mul_one]
    exact subtract_telescope _ _ _

theorem commutes_pow (D R : A) (hcomm : D * R = R * D) (n : Nat) :
    D * R ^ n = R ^ n * D := by
  induction n with
  | zero => simp only [Semiring.pow_zero, Semiring.mul_one, Semiring.one_mul]
  | succ n ih =>
    simp only [Semiring.pow_succ]
    rw [← Semiring.mul_assoc D, ih, Semiring.mul_assoc _ D, hcomm,
      ← Semiring.mul_assoc]

theorem commutes_geometricSum (D R : A) (hcomm : D * R = R * D) (n : Nat) :
    D * geometricSum R n = geometricSum R n * D := by
  induction n with
  | zero => simp only [geometricSum, Semiring.mul_zero, Semiring.zero_mul]
  | succ n ih =>
    simp only [geometricSum]
    have hp := commutes_pow D R hcomm n
    rw [Semiring.left_distrib, Semiring.right_distrib, ih, hp]

/-- Defect of a proposed contraction for the differential `D`. -/
def contractionDefect (D h : A) : A := 1 - D * h - h * D

theorem differential_commutes_defect (D h : A) (hD : D * D = 0) :
    D * contractionDefect D h = contractionDefect D h * D := by
  unfold contractionDefect
  simp only [mul_sub, sub_mul, Semiring.mul_one, Semiring.one_mul]
  have hz₁ : D * (D * h) = 0 := by
    rw [← Semiring.mul_assoc, hD, Semiring.zero_mul]
  have hz₂ : h * D * D = 0 := by
    rw [Semiring.mul_assoc, hD, Semiring.mul_zero]
  rw [hz₁, hz₂, ← Semiring.mul_assoc D h D]
  simp only [Ring.sub_eq_add_neg, AddCommGroup.neg_zero, Semiring.add_zero]

/-- A finite correction to the candidate contracting homotopy. -/
def correctedContraction (D h : A) (n : Nat) : A :=
  h * geometricSum (contractionDefect D h) n

/--
Exact finite correction formula.  A separate explicit norm bound on the
right-hand residual is all that is needed for an approximate contraction.
-/
theorem correctedContraction_residual (D h : A) (hD : D * D = 0) (n : Nat) :
    D * correctedContraction D h n + correctedContraction D h n * D =
      1 - contractionDefect D h ^ n := by
  have hc := differential_commutes_defect D h hD
  have hs := commutes_geometricSum D (contractionDefect D h) hc n
  have hg := geometric_left (contractionDefect D h) n
  unfold correctedContraction
  rw [Semiring.mul_assoc h _ D, ← hs, ← Semiring.mul_assoc,
    ← Semiring.mul_assoc, ← Semiring.right_distrib]
  have hfactor : D * h + h * D = 1 - contractionDefect D h := by
    unfold contractionDefect
    simp only [Ring.sub_eq_add_neg, AddCommGroup.neg_add, AddCommGroup.neg_neg,
      ← Semiring.add_assoc, AddCommGroup.add_neg_cancel, AddCommMonoid.zero_add]
  rw [hfactor]
  exact hg

#print axioms pow_commutes
#print axioms geometric_left
#print axioms geometric_right
#print axioms commutes_pow
#print axioms commutes_geometricSum
#print axioms differential_commutes_defect
#print axioms correctedContraction_residual

end ObservableAnalysis
