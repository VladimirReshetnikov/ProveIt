import Mathlib

/-!
# Finite exact expectation: ambient Lean blueprint

STATUS: uncompiled blueprint, not a completed formalization.

The file introduces no theorem axiom and contains no `sorry`.  The structures
at the end are proof obligations to be constructed.  The object-language
endpoint is in `ObjectLanguageTargets.lean`.
-/

namespace ExpectedValueIPRA

open scoped BigOperators

/-- A finite probability law represented by natural multiplicities. -/
structure FinLaw where
  card : Nat
  weight : Fin card -> Nat
  total : Nat
  total_pos : 0 < total
  weight_sum : (∑ i, weight i) = total

namespace FinLaw

/-- Exact probability of a decidable event. -/
def prob (L : FinLaw) (A : Fin L.card -> Bool) : Rat :=
  (∑ i, if A i then (L.weight i : Rat) else 0) / L.total

/-- Exact expectation of a rational observable. -/
def expect (L : FinLaw) (X : Fin L.card -> Rat) : Rat :=
  (∑ i, (L.weight i : Rat) * X i) / L.total

/-- Mean of a distinguished observable. -/
def mean (L : FinLaw) (X : Fin L.card -> Rat) : Rat := L.expect X

/-- Raw moment. -/
def moment (L : FinLaw) (X : Fin L.card -> Rat) (r : Nat) : Rat :=
  L.expect (fun i => (X i) ^ r)

/-- Variance. -/
def variance (L : FinLaw) (X : Fin L.card -> Rat) : Rat :=
  let mu := L.expect X
  L.expect (fun i => (X i - mu) ^ 2)

/-- Exact finite CDF at a rational threshold. -/
def cdf (L : FinLaw) (X : Fin L.card -> Rat) (q : Rat) : Rat :=
  L.prob (fun i => decide (X i <= q))

/-- Almost-sure equality in the natural-weight presentation. -/
def AeEq (L : FinLaw) (X Y : Fin L.card -> Rat) : Prop :=
  (∑ i, if X i = Y i then 0 else L.weight i) = 0

/-- Product law.  A completed file proves the weight-sum field by finite
Fubini and multiplication of the two normalization equations. -/
structure ProductData (A B : FinLaw) where
  law : FinLaw
  indexEquiv : Fin law.card ≃ (Fin A.card × Fin B.card)
  weight_rule : ∀ k,
    law.weight k = A.weight (indexEquiv k).1 * B.weight (indexEquiv k).2
  total_rule : law.total = A.total * B.total

/-- Pushforward fiber mass for finite LOTUS. -/
def fiberWeight (L : FinLaw) (code : Fin L.card -> Nat) (v : Nat) : Nat :=
  ∑ i, if code i = v then L.weight i else 0

/-- Cell mass of a finite partition. -/
def cellWeight {k : Nat} (L : FinLaw) (part : Fin L.card -> Fin k) (c : Fin k) : Nat :=
  ∑ i, if part i = c then L.weight i else 0

/-- Conditional mean on a cell, with zero chosen on null cells. -/
def condMean {k : Nat} (L : FinLaw) (X : Fin L.card -> Rat)
    (part : Fin L.card -> Fin k) (c : Fin k) : Rat :=
  let m := L.cellWeight part c
  if h : m = 0 then 0
  else (∑ i, if part i = c then (L.weight i : Rat) * X i else 0) / m

end FinLaw

/-- A finite theorem package to be constructed in ambient Lean. -/
structure FiniteExpectationProofPackage where
  expect_one : ∀ L : FinLaw, L.expect (fun _ => 1) = 1
  expect_const : ∀ (L : FinLaw) (c : Rat), L.expect (fun _ => c) = c
  expect_add : ∀ (L : FinLaw) (X Y : Fin L.card -> Rat),
    L.expect (fun i => X i + Y i) = L.expect X + L.expect Y
  expect_smul : ∀ (L : FinLaw) (a : Rat) (X : Fin L.card -> Rat),
    L.expect (fun i => a * X i) = a * L.expect X
  nonnegative : ∀ (L : FinLaw) (X : Fin L.card -> Rat),
    (∀ i, 0 <= X i) -> 0 <= L.expect X
  monotone : ∀ (L : FinLaw) (X Y : Fin L.card -> Rat),
    (∀ i, X i <= Y i) -> L.expect X <= L.expect Y
  convexHull : ∀ (L : FinLaw) (X : Fin L.card -> Rat) (a b : Rat),
    (∀ i, a <= X i ∧ X i <= b) -> a <= L.expect X ∧ L.expect X <= b
  ae_congr : ∀ (L : FinLaw) (X Y : Fin L.card -> Rat),
    L.AeEq X Y -> L.expect X = L.expect Y
  abs_expect_le : ∀ (L : FinLaw) (X : Fin L.card -> Rat),
    |L.expect X| <= L.expect (fun i => |X i|)
  indicator : ∀ (L : FinLaw) (A : Fin L.card -> Bool),
    L.expect (fun i => if A i then 1 else 0) = L.prob A

  /-- Finite discrete LOTUS, stated with a natural code for the image. -/
  lotus : ∀ (L : FinLaw) (code : Fin L.card -> Nat) (g : Nat -> Rat),
    L.expect (fun i => g (code i)) =
      (∑ v in Finset.range (1 + Finset.univ.sup code),
        (L.fiberWeight code v : Rat) * g v) / L.total

  /-- Bounded nonnegative integer tail sum. -/
  tailSum : ∀ (L : FinLaw) (X : Fin L.card -> Nat) (B : Nat),
    (∀ i, X i <= B) ->
    L.expect (fun i => (X i : Rat)) =
      ∑ k in Finset.range B, L.prob (fun i => decide (k < X i))

  variance_identity : ∀ (L : FinLaw) (X : Fin L.card -> Rat),
    L.variance X = L.moment X 2 - (L.expect X)^2

  markov : ∀ (L : FinLaw) (X : Fin L.card -> Rat) (a : Rat),
    0 < a -> (∀ i, 0 <= X i) ->
    L.prob (fun i => decide (a <= X i)) <= L.expect X / a

  chebyshev : ∀ (L : FinLaw) (X : Fin L.card -> Rat) (a : Rat),
    0 < a ->
    L.prob (fun i => decide (a <= |X i - L.expect X|)) <= L.variance X / a^2

  cauchySchwarz : ∀ (L : FinLaw) (X Y : Fin L.card -> Rat),
    (L.expect (fun i => X i * Y i))^2 <=
      L.expect (fun i => X i^2) * L.expect (fun i => Y i^2)

  /-- Supporting-line form of finite Jensen. -/
  jensenCertificate : ∀ (L : FinLaw) (X : Fin L.card -> Rat)
      (f : Rat -> Rat) (s b : Rat),
    f (L.expect X) = s * L.expect X + b ->
    (∀ i, s * X i + b <= f (X i)) ->
    f (L.expect X) <= L.expect (fun i => f (X i))

/-- Independence/product and conditional-expectation obligations. -/
structure FiniteDependenceProofPackage (core : FiniteExpectationProofPackage) where
  productExpectation : ∀ (A B : FinLaw) (P : A.ProductData B)
      (X : Fin A.card -> Rat) (Y : Fin B.card -> Rat),
    P.law.expect (fun k => X (P.indexEquiv k).1 * Y (P.indexEquiv k).2) =
      A.expect X * B.expect Y

  totalExpectation : ∀ {k : Nat} (L : FinLaw) (X : Fin L.card -> Rat)
      (part : Fin L.card -> Fin k),
    L.expect (fun i => L.condMean X part (part i)) = L.expect X

/-- Sample-mean and finite maximal-inequality obligations. -/
structure SampleProofPackage (core : FiniteExpectationProofPackage) where
  sampleMeanUnbiased : Prop
  sampleMeanVariance : Prop
  residualSquares : Prop
  kolmogorovMaximal : Prop
  finiteHorizonStrongLaw : Prop

/-!
The intended next step is denominator clearing.  Every rational observable is
converted to a signed numerator over one common positive denominator; every
statement above then becomes an equality or inequality of primitive-recursive
natural terms.  `ObjectLanguageTargets.lean` records that endpoint.
-/

end ExpectedValueIPRA
