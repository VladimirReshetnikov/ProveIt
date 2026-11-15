import Mathlib

/-!
# Finite approximation specifications

STATUS: uncompiled semantic specifications only.

These concrete rational predicates describe the finite claims in the
accompanying paper. This file does not assert an existence theorem, prove
the reference algorithms correct, or construct an object-iPRA derivation.
The predicates must still be reified as `Fm PTm` formulas and proved using
`Prf PRAAx`; an ambient theorem about these predicates would not itself
perform that internalization.

Target environment: ProveIt commit
6ad3d9f37184ac242a8946f1c5d45a5603cf57f2, Lean/mathlib v4.32.0.
-/

namespace DirichletKroneckerIPRA.Spec

open scoped BigOperators

abbrev RatVector (d : Nat) := Fin d → Rat
abbrev IntVector (d : Nat) := Fin d → Int
abbrev RatMatrix (m d : Nat) := Fin m → Fin d → Rat

/-- Exact rational distance to the nearest integer. -/
def rhoQ (x : Rat) : Rat :=
  let lower : Int := Int.floor x
  let residue : Rat := x - (lower : Rat)
  min residue (1 - residue)

def dotQ {d : Nat} (h : IntVector d) (x : RatVector d) : Rat :=
  ∑ j, (h j : Rat) * x j

def heightBound {d : Nat} (h : IntVector d) (H : Nat) : Prop :=
  ∀ j, (h j).natAbs ≤ H

def maxNonnegative {m : Nat} (x : RatVector m) : Rat :=
  (List.ofFn x).foldl max 0

def relationSize {m d : Nat} (matrix : RatMatrix m d)
    (h : IntVector d) : Rat :=
  maxNonnegative (fun i => rhoQ (dotQ h (matrix i)))

structure ScalarInput where
  value : Rat
  bound : Nat

structure ScalarWitness where
  numerator : Int
  denominator : Nat

def ScalarInputValid (input : ScalarInput) : Prop :=
  1 ≤ input.bound

/-- Sharp rational claim; this predicate carries no existence proof. -/
def SharpScalarOutput (input : ScalarInput) (w : ScalarWitness) : Prop :=
  1 ≤ w.denominator ∧ w.denominator ≤ input.bound ∧
    |(w.denominator : Rat) * input.value - (w.numerator : Rat)| ≤
      1 / ((input.bound : Rat) + 1)

structure ScalarTransferInput where
  sample : Rat
  inputError : Rat
  bound : Nat

def ScalarTransferInputValid (input : ScalarTransferInput) : Prop :=
  1 ≤ input.bound ∧ 0 ≤ input.inputError ∧
    input.inputError ≤
      1 / (2 * (input.bound : Rat)^2 * ((input.bound : Rat) + 1))

def ScalarTransferOutput (input : ScalarTransferInput)
    (w : ScalarWitness) : Prop :=
  1 ≤ w.denominator ∧ w.denominator ≤ input.bound ∧
    |(w.denominator : Rat) * input.sample - (w.numerator : Rat)| +
      (w.denominator : Rat) * input.inputError < 1 / (input.bound : Rat)

structure SimultaneousInput (d : Nat) where
  samples : RatVector d
  inputError : Rat
  bound : Nat

structure SimultaneousWitness (d : Nat) where
  numerators : IntVector d
  denominator : Nat
  side : Rat

def SimultaneousInputValid {d : Nat} (input : SimultaneousInput d) : Prop :=
  1 ≤ d ∧ 1 ≤ input.bound ∧ 0 ≤ input.inputError ∧
    input.inputError ≤
      1 / ((input.bound : Rat) *
        (4 * (d : Rat) * (input.bound : Rat) * (2 * (input.bound : Rat) + 1)))

/-- The root-free conclusion is `N * side^d < 1`. -/
def SimultaneousOutput {d : Nat} (input : SimultaneousInput d)
    (w : SimultaneousWitness d) : Prop :=
  1 ≤ w.denominator ∧ w.denominator ≤ input.bound ∧ 0 < w.side ∧
    (input.bound : Rat) * w.side^d < 1 ∧
    ∀ j, |(w.denominator : Rat) * input.samples j - (w.numerators j : Rat)| +
      (w.denominator : Rat) * input.inputError < w.side

structure SimultaneousGridParameters where
  height : Nat
  subdivision : Nat
  thresholdIndex : Nat
  innerSide : Rat
  outerSide : Rat
  firstCount : Nat
  otherCount : Nat

def SimultaneousGridValid (d N : Nat) (g : SimultaneousGridParameters) : Prop :=
  1 ≤ d ∧ 1 ≤ N ∧
    g.height = 4*d*N*(2*N+1) ∧
    g.subdivision = 16*N*d*(N+1) ∧
    1 ≤ g.thresholdIndex ∧ g.thresholdIndex < g.height ∧
    g.innerSide = (g.thresholdIndex : Rat) / (g.height : Rat) ∧
    g.outerSide = ((g.thresholdIndex : Rat) + 1) / (g.height : Rat) ∧
    0 < g.innerSide ∧ g.innerSide < g.outerSide ∧
    (N : Rat) * g.outerSide^d < 1 ∧
    (g.firstCount : Rat) = (g.subdivision : Rat) * ((N : Rat) + 1/2) ∧
    (g.otherCount : Int) = Int.floor ((g.subdivision : Rat) * g.innerSide) ∧
    1 ≤ g.otherCount ∧
    g.subdivision^(d+1) < g.firstCount * g.otherCount^d

structure KroneckerParameters where
  accuracy : Nat
  constant : Nat
  frequencyHeight : Nat
  centralDenominator : Nat
  searchSide : Nat

def KroneckerParametersValid (d : Nat) (k : KroneckerParameters) : Prop :=
  1 ≤ d ∧ 2 ≤ k.accuracy ∧ 1 ≤ k.constant ∧
    k.frequencyHeight =
      4 * 3^d * (d+1)^(d+1) * (2*k.accuracy)^(2*d+2) ∧
    k.centralDenominator = (2*k.frequencyHeight+1)^d ∧
    k.searchSide = 32*k.constant*k.centralDenominator

structure CompatibilityInput (m d : Nat) where
  matrix : RatMatrix m d
  target : RatVector d
  height : Nat
  constant : Nat
  inputError : Rat

def compatibilityError {m d : Nat} (input : CompatibilityInput m d) : Rat :=
  (d : Rat) * (input.height : Rat) * input.inputError

def targetUpper {m d : Nat} (input : CompatibilityInput m d)
    (h : IntVector d) : Rat :=
  rhoQ (dotQ h input.target) + compatibilityError input

def generatorLower {m d : Nat} (input : CompatibilityInput m d)
    (h : IntVector d) : Rat :=
  maxNonnegative (fun i =>
    max 0 (rhoQ (dotQ h (input.matrix i)) - compatibilityError input))

/-- Finite rational table condition, before Boolean-fold reification. -/
def IntervalCertificateValid {m d : Nat} (input : CompatibilityInput m d) : Prop :=
  1 ≤ m ∧ 1 ≤ d ∧ 1 ≤ input.height ∧ 1 ≤ input.constant ∧
    0 ≤ input.inputError ∧
    input.inputError ≤
      1 / (64 * (d : Rat) * (input.height : Rat) * ((input.constant : Rat) + 1)) ∧
    ∀ h : IntVector d, heightBound h input.height →
      targetUpper input h ≤ 1/8 + (input.constant : Rat) * generatorLower input h

def FiniteCompatibility {m d : Nat} (matrix : RatMatrix m d)
    (target : RatVector d) (H C : Nat) : Prop :=
  ∀ h : IntVector d, heightBound h H →
    rhoQ (dotQ h target) ≤ 1/8 + (C : Rat) * relationSize matrix h

structure KroneckerWitness (m d : Nat) where
  coefficients : IntVector m
  integerPart : IntVector d

def orbitResidual {m d : Nat} (matrix : RatMatrix m d)
    (target : RatVector d) (w : KroneckerWitness m d) (j : Fin d) : Rat :=
  (∑ i, (w.coefficients i : Rat) * matrix i j) -
    (w.integerPart j : Rat) - target j

def KroneckerOutput {m d : Nat} (matrix : RatMatrix m d)
    (target : RatVector d) (s N : Nat) (w : KroneckerWitness m d) : Prop :=
  (∀ i, (w.coefficients i).natAbs < N) ∧
    ∀ j, |orbitResidual matrix target w j| < 1 / (s : Rat)

/-- The exact rational test used to choose a candidate. -/
def AcceptedOrbit {m d : Nat} (matrix : RatMatrix m d)
    (target : RatVector d) (s : Nat) (w : KroneckerWitness m d) : Prop :=
  ∀ j, |orbitResidual matrix target w j| < 3 / (4 * (s : Rat))

def coefficientSize {m d : Nat} (w : KroneckerWitness m d) : Nat :=
  ∑ i, (w.coefficients i).natAbs

def OrbitInputErrorValid (m s N : Nat) (inputError : Rat) : Prop :=
  1 ≤ m ∧ 2 ≤ s ∧ 1 ≤ N ∧ 0 ≤ inputError ∧
    inputError ≤ 1 / (8 * (s : Rat) * ((m*(N-1)+1 : Nat) : Rat))

/-- Certified error for named inputs whose coordinates have this error. -/
def KroneckerTransferOutput {m d : Nat} (matrix : RatMatrix m d)
    (target : RatVector d) (s N : Nat) (inputError : Rat)
    (w : KroneckerWitness m d) : Prop :=
  (∀ i, (w.coefficients i).natAbs < N) ∧
    ∀ j, |orbitResidual matrix target w j| +
      ((coefficientSize w : Rat) + 1) * inputError < 7 / (8 * (s : Rat))

structure RelationObstruction (d : Nat) where
  coefficients : IntVector d

def ExactObstruction {m d : Nat} (matrix : RatMatrix m d)
    (target : RatVector d) (w : RelationObstruction d) : Prop :=
  (∀ i, rhoQ (dotQ w.coefficients (matrix i)) = 0) ∧
    0 < rhoQ (dotQ w.coefficients target)

def NearObstruction {m d : Nat} (matrix : RatMatrix m d)
    (target : RatVector d) (H C : Nat) (w : RelationObstruction d) : Prop :=
  heightBound w.coefficients H ∧
    1/16 + (C : Rat) * relationSize matrix w.coefficients <
      rhoQ (dotQ w.coefficients target)

end DirichletKroneckerIPRA.Spec
