import Std

/-!
# Finite series contracts: definitions and explicit proof targets

This file compiles with Lean 4.32.0 and `Std` only.  It is a specification,
not a formal proof of the manuscript's series-contraction theorem.
There are no new axioms and no `sorry`s.  The unproved mathematical goals
are declarations of type `Prop`, not assumptions or disguised theorems.

`QPoly` stores finite rational coefficient arrays.  Arrays at precision `K`
represent polynomials modulo X^(K+1).  The companion Python reference uses
the same operations.  The complex extension uses pairs of these arrays
and the norm |re|+|im|, with the same convolution proof.
-/

namespace IPRAFramework.Series

abbrev QPoly := List Rat

def qabs (q : Rat) : Rat := if q < 0 then -q else q

def dyadic (s : Nat) : Rat := mkRat 1 (2 ^ s)

def coeff (p : QPoly) (k : Nat) : Rat := p[k]?.getD 0

def qsum (xs : List Rat) : Rat := xs.foldl (· + ·) 0

def zero (K : Nat) : QPoly := List.replicate (K + 1) 0

def one (K : Nat) : QPoly := 1 :: List.replicate K 0

def truncate (K : Nat) (p : QPoly) : QPoly :=
  (List.range (K + 1)).map (coeff p)

def add (K : Nat) (p q : QPoly) : QPoly :=
  (List.range (K + 1)).map (fun k => coeff p k + coeff q k)

def sub (K : Nat) (p q : QPoly) : QPoly :=
  (List.range (K + 1)).map (fun k => coeff p k - coeff q k)

def mul (K : Nat) (p q : QPoly) : QPoly :=
  (List.range (K + 1)).map fun k =>
    qsum ((List.range (k + 1)).map (fun i => coeff p i * coeff q (k - i)))

def pow (K : Nat) (p : QPoly) : Nat → QPoly
  | 0 => one K
  | n + 1 => mul K (pow K p n) p

def scaleShift (K i : Nat) (c : Rat) (p : QPoly) : QPoly :=
  (List.range (K + 1)).map (fun k => if i ≤ k then c * coeff p (k - i) else 0)

structure Monomial where
  xDegree : Nat
  zDegree : Nat
  coefficient : Rat
  deriving Repr, DecidableEq

abbrev Operator := List Monomial

def apply (K : Nat) (F : Operator) (p : QPoly) : QPoly :=
  F.foldl (fun acc t => add K acc
    (scaleShift K t.xDegree t.coefficient (pow K p t.zDegree))) (zero K)

def iterate (K : Nat) (F : Operator) : Nat → QPoly
  | 0 => zero K
  | n + 1 => apply K F (iterate K F n)

def weightedNorm (K : Nat) (R : Rat) (p : QPoly) : Rat :=
  qsum ((List.range (K + 1)).map (fun k => qabs (coeff p k) * R ^ k))

def constantBound (F : Operator) (R : Rat) : Rat :=
  qsum (F.map (fun t => if t.zDegree = 0 then
    qabs t.coefficient * R ^ t.xDegree else 0))

def contractionBound (F : Operator) (R rho : Rat) : Rat :=
  qsum (F.map (fun t => if t.zDegree = 0 then 0 else
    (t.zDegree : Rat) * qabs t.coefficient * R ^ t.xDegree * rho ^ (t.zDegree - 1)))

def Certificate (F : Operator) (R rho : Rat) : Prop :=
  0 < R ∧ R ≤ 1 ∧ 0 < rho ∧ rho ≤ 1 ∧
  constantBound F R ≤ rho / 2 ∧ contractionBound F R rho ≤ 1 / 2

instance (F : Operator) (R rho : Rat) : Decidable (Certificate F R rho) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! The four principal finite targets.  These are NOT proved in this file. -/

def NormSubmultiplicative : Prop :=
  ∀ K R (p q : QPoly), 0 ≤ R →
    weightedNorm K R (mul K p q) ≤ weightedNorm K R p * weightedNorm K R q

def ContractionTarget : Prop :=
  ∀ K F R rho (p q : QPoly), Certificate F R rho →
    weightedNorm K R p ≤ rho → weightedNorm K R q ≤ rho →
    weightedNorm K R (sub K (apply K F p) (apply K F q)) ≤
      (1 / 2) * weightedNorm K R (sub K p q)

def InvarianceTarget : Prop :=
  ∀ K F R rho (p : QPoly), Certificate F R rho →
    weightedNorm K R p ≤ rho → weightedNorm K R (apply K F p) ≤ rho

def PicardTarget : Prop :=
  ∀ K F R rho n m, Certificate F R rho → n ≤ m →
    weightedNorm K R (iterate K F n) ≤ rho ∧
    weightedNorm K R (sub K (iterate K F m) (iterate K F n)) ≤ rho * dyadic n

def CoefficientTarget : Prop :=
  ∀ K F r h n m k, Certificate F (dyadic r) (dyadic h) →
    n ≤ m → k ≤ K →
    qabs (coeff (iterate K F m) k - coeff (iterate K F n) k) ≤
      dyadic h * (2 : Rat) ^ (r * k) * dyadic n

/-- Exact-rational input case: no rounding error in the finite iteration. -/
def coefficientName (F : Operator) (r k s : Nat) : Rat :=
  coeff (iterate k F (s + r * k + 3)) k

def FastCauchy (a : Nat → Rat) : Prop :=
  ∀ s t, s ≤ t → qabs (a s - a t) ≤ dyadic s

def CoefficientNameTarget : Prop :=
  ∀ F r h k, Certificate F (dyadic r) (dyadic h) →
    FastCauchy (coefficientName F r k)

/-!
For represented input coefficients, replace each stored coefficient by a
fixed evaluator `parameter → i → j → precision → Rat × Rat`.  Supply its
fast-Cauchy contract and finite rational upper enclosures.  At degree k and
precision s compute the same truncated iterate number s+r*k+3; approximate
that finite expression to 2^(-s-3).  The manuscript proves the necessary
finite error bounds.  No evaluator for arbitrary PR programs is used.

The formal substitution target at degree K is equality of the first K+1
coefficient names of C and F(X,C), where names are equal when their
differences are bounded by every dyadic tolerance.  Each coefficient uses
only finite convolution; a common iteration horizon supplies its proof.

Object-theory completion: represent each listed array operation by a
specific `PR` term; clear positive rational denominators; encode all bounded
conjunctions by Boolean folds; construct the `PRA.qfInd` proofs of norm and
increment invariants.  A host proof of `PicardTarget` alone does not perform
this object-language derivation.
-/

theorem iterate_zero (K : Nat) (F : Operator) : iterate K F 0 = zero K := rfl

theorem iterate_succ (K : Nat) (F : Operator) (n : Nat) :
    iterate K F (n + 1) = apply K F (iterate K F n) := rfl

/-- P=Y²-(1+alpha+X), centre 1, approximate inverse 1/2. -/
def squareRootOperator (alpha : Rat) : Operator :=
  [⟨0, 0, alpha / 2⟩, ⟨1, 0, 1 / 2⟩, ⟨0, 2, -(1 / 2)⟩]

-- Closed exact-rational examples checked by Lean's kernel.
example : Certificate (squareRootOperator (1 / 16)) (1 / 8) (1 / 4) := by decide +kernel

example : Certificate (squareRootOperator (-1 / 16)) (1 / 8) (1 / 4) := by decide +kernel

example : Certificate (squareRootOperator 0) (1 / 8) (1 / 4) := by decide +kernel

example : coeff (iterate 2 (squareRootOperator 0) 2) 1 = 1 / 2 := by decide +kernel

example : coeff (iterate 2 (squareRootOperator 0) 2) 2 = -(1 / 8) := by decide +kernel

end IPRAFramework.Series
