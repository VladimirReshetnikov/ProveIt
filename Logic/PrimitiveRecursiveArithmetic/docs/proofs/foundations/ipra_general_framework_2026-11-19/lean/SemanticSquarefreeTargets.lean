import Mathlib

/-!
# Semantic specifications for the squarefree norm producer

STATUS: unelaborated definitions of proof obligations, not proved theorems.
These are ordinary Lean propositions over rational polynomials. They are
NOT object-iPRA derivations. RuntimeNormTargets.lean and the accompanying
roadmap describe the distinct numerical `Prf PRAAx` implementation.

In particular, `derivativeCoprime` is an explicit Bezout equation. It does
not use Mathlib's potentially different `Squarefree` terminology over an
arbitrary imperfect field. Rational coefficients are fixed here.
-/

open scoped BigOperators

namespace QuantitativeElimination.Semantic

abbrev QPoly := Polynomial ℚ

def derivativeCoprime (f : QPoly) : Prop :=
  ∃ u v : QPoly, u * f + v * f.derivative = 1

def reducedQuotient (f : QPoly) : Prop :=
  ∀ (b : QPoly) (n : ℕ), 1 ≤ n → f ∣ b ^ n → f ∣ b

def companion (f : QPoly) (m : ℕ) : Matrix (Fin m) (Fin m) QPoly :=
  fun i j =>
    if j.val + 1 = m then
      if i.val = 0 then f else 0
    else if i.val = j.val + 1 then 1 else 0

def multiplicationMatrix {m : ℕ} (f : QPoly) (rows : Fin m → QPoly) :
    Matrix (Fin m) (Fin m) QPoly :=
  ∑ j : Fin m, rows j • companion f m ^ j.val

def norm {m : ℕ} (f : QPoly) (rows : Fin m → QPoly) : QPoly :=
  (multiplicationMatrix f rows).det

def rowsNonzero {m : ℕ} (rows : Fin m → QPoly) : Prop :=
  ∃ j : Fin m, rows j ≠ 0

def weightBound {m : ℕ} (rows : Fin m → QPoly) (d W : ℕ) : Prop :=
  ∀ (j : Fin m) (i : ℕ), (rows j).coeff i ≠ 0 → m * i + d * j.val ≤ W

def evaluateRows {m : ℕ} (rows : Fin m → QPoly) (x y : ℚ) : ℚ :=
  ∑ j : Fin m, (rows j).eval x * y ^ j.val

def ReducednessGoal : Prop :=
  ∀ f : QPoly, 1 ≤ f.natDegree → derivativeCoprime f → reducedQuotient f

def SquarefreeNormGoal : Prop :=
  ∀ (m : ℕ) (f : QPoly) (rows : Fin m → QPoly) (W : ℕ),
    1 ≤ m → 1 ≤ f.natDegree → derivativeCoprime f →
    rowsNonzero rows → weightBound rows f.natDegree W →
      norm f rows ≠ 0 ∧ (norm f rows).natDegree ≤ W

def FiniteZeroCountGoal : Prop :=
  ∀ (m : ℕ) (f : QPoly) (rows : Fin m → QPoly) (W : ℕ)
    (points : List (ℚ × ℚ)),
    1 ≤ m → 1 ≤ f.natDegree → derivativeCoprime f →
    rowsNonzero rows → weightBound rows f.natDegree W →
    points.Nodup →
    (∀ p ∈ points, p.2 ^ m = f.eval p.1 ∧ evaluateRows rows p.1 p.2 = 0) →
    points.length ≤ W

-- These #checks expose targets, not proofs.
#check ReducednessGoal
#check SquarefreeNormGoal
#check FiniteZeroCountGoal

end QuantitativeElimination.Semantic
