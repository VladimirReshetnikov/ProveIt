import Std

/-!
# Root-support constructions: executable definitions and UNPROVED targets

Compilation checks definitions and proposition syntax, not the named targets.
There are no axiom declarations, `sorry` proofs, or assertions of completed
object-iPRA derivations. A root engine is an explicit input here. The report
constructs a PR engine from the repository's written rational-descent lemma;
formalizing that lemma remains an identified dependency.

Host function parameters are interfaces. In object arithmetic use one fixed
PR coefficient evaluator, finite tables, and PR code for all finite loops.
The declarations below do not assert that arbitrary Lean functions are PR.
-/

namespace IPRADemand.RootSets

structure GQ where
  re : Rat
  im : Rat
  deriving Repr, DecidableEq

def zero : GQ := ⟨0, 0⟩
def one : GQ := ⟨1, 0⟩
def add (z w : GQ) : GQ := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : GQ) : GQ := ⟨-z.re, -z.im⟩
def sub (z w : GQ) : GQ := add z (neg w)
def mul (z w : GQ) : GQ :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def normSq (z : GQ) : Rat := z.re * z.re + z.im * z.im
def qabs (q : Rat) : Rat := if q < 0 then -q else q
def normOne (z : GQ) : Rat := qabs z.re + qabs z.im
def dyadic (s : Nat) : Rat := mkRat 1 (2 ^ s)

def gpow (z : GQ) : Nat → GQ
  | 0 => one
  | n + 1 => mul (gpow z n) z

abbrev Poly := List GQ
def coeff (p : Poly) (i : Nat) : GQ := p[i]?.getD zero

def eval (p : Poly) (z : GQ) : GQ :=
  p.foldr (fun a acc => add a (mul z acc)) zero

def addPoly : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => add a b :: addPoly p q

def mulPoly : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => addPoly (q.map (mul a)) (zero :: mulPoly p q)

def productPoly (zs : List GQ) : Poly :=
  zs.foldl (fun p z => mulPoly p [neg z, one]) [one]

def coefficientError (p q : Poly) : Rat :=
  (List.range (max p.length q.length)).foldl
    (fun acc i => acc + normOne (sub (coeff p i) (coeff q i))) 0

def monicPositive (p : Poly) : Prop :=
  1 < p.length ∧ coeff p (p.length - 1) = one

def cover (s t : List GQ) (r : Rat) : Bool :=
  s.all (fun z => t.any (fun w => decide (normSq (sub z w) ≤ r * r)))

def close (s t : List GQ) (r : Rat) : Bool :=
  cover s t r && cover t s r

def bounded (s : List GQ) (R : Rat) : Prop :=
  ∀ z ∈ s, normSq z ≤ R * R

def coefficientGap (p q : Poly) (n : Nat) (δ : Rat) : Prop :=
  ∀ i, i < n → normSq (sub (coeff p i) (coeff q i)) ≤ δ * δ

/-- UNPROVED finite squared-norm product stability proposition. -/
def ProductStabilityTarget : Prop :=
  ∀ (s t : List GQ) (R δ r : Rat),
    0 < s.length → s.length = t.length →
    1 ≤ R → 0 ≤ δ → 0 ≤ r → bounded s R → bounded t R →
    coefficientGap (productPoly s) (productPoly t) s.length δ →
    (s.length : Rat) * R ^ (s.length - 1) * δ ≤ r ^ s.length →
    close s t r = true

def syntheticQuotient (p : Poly) (z : GQ) : Poly :=
  (List.range (p.length - 1)).map (fun i =>
    (List.range p.length).foldl (fun acc j =>
      if i < j then add acc (mul (coeff p j) (gpow z (j - i - 1)))
      else acc) zero)

abbrev RootEngine := Poly → Rat → GQ

def ApproxRootSpec (root : RootEngine) : Prop :=
  ∀ p ε, monicPositive p → 0 < ε → ε ≤ 1 →
    normSq (eval p (root p ε)) ≤ ε * ε

/-! ## Bounded approximate roots from a supplied descent step

`DescentMap` returns the NEXT point (not merely the displacement).
All contracts below use only rational squared-norm comparisons. The finite
root constructor is implemented; its correctness target is not proved.
-/

abbrev DescentMap := Poly → GQ → GQ

def descentDenominator (d : Nat) : Nat := 2 ^ d * 4 ^ (2 * d * d)

def descentContraction (d : Nat) : Rat :=
  1 - 1 / (4 * (descentDenominator d : Rat))

def RationalDescentSpec (step : DescentMap) : Prop :=
  ∀ p z, monicPositive p →
    normSq (eval p (step p z)) ≤
      descentContraction (p.length - 1) ^ 2 * normSq (eval p z)

/-- Ceiling on nonnegative rationals; the definition is total on all Rat. -/
def positiveCeiling (q : Rat) : Nat :=
  (q.num.toNat + q.den - 1) / q.den

def initialResidualBound (p : Poly) : Rat :=
  let b := normOne (coeff p 0)
  if 1 ≤ b then b else 1

def rootIterationBudget (p : Poly) (ε : Rat) : Nat :=
  4 * descentDenominator (p.length - 1) *
    positiveCeiling (initialResidualBound p / ε)

def descentIterate (step : DescentMap) (p : Poly) : Nat → GQ
  | 0 => zero
  | k + 1 => step p (descentIterate step p k)

def rootFromDescent (step : DescentMap) : RootEngine :=
  fun p ε => descentIterate step p (rootIterationBudget p ε)

/-- UNPROVED bridge: J=4*D*ceil(B/epsilon) suffices by finite Bernoulli. -/
def DescentToApproxRootTarget : Prop :=
  ∀ step, RationalDescentSpec step → ApproxRootSpec (rootFromDescent step)

def numeratorBound (z : GQ) : Nat :=
  z.re.num.natAbs + z.im.num.natAbs

/-- A deliberately generous integer bound; Rat denominators are positive. -/
def initialBound (p : Poly) : Nat :=
  1 + p.foldl (fun acc z => acc + numeratorBound z) 0

def boundBudget (n : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | A, k + 1 =>
    let T := 2 * A + 5
    T * boundBudget n ((A + 1) * T ^ n) k

def factorLoop (root : RootEngine) (ε : Rat) : Nat → Poly → List GQ
  | 0, _ => []
  | k + 1, p =>
    let z := root p ε
    z :: factorLoop root ε k (syntheticQuotient p z)

def approximateFactor (root : RootEngine) (p : Poly) (η : Rat) : List GQ :=
  let n := p.length - 1
  let L := boundBudget n (initialBound p) n
  let ε := η / (2 * (n : Rat) * (L : Rat))
  factorLoop root ε n p

/-- UNPROVED semantic theorem relative to an approximate-root engine. -/
def ApproxFactorGivenRootTarget : Prop :=
  ∀ root, ApproxRootSpec root → ∀ p η,
    monicPositive p → 0 < η → η ≤ 1 →
    (approximateFactor root p η).length = p.length - 1 ∧
    coefficientError p (productPoly (approximateFactor root p η)) ≤ η

abbrev CoefficientNames := Nat → Nat → GQ

def FastCoefficients (a : CoefficientNames) (n : Nat) : Prop :=
  ∀ i, i < n → ∀ s t,
    normSq (sub (a i s) (a i t)) ≤ (dyadic s + dyadic t) ^ 2

def nameBound (a : CoefficientNames) (n : Nat) : Nat :=
  3 + (List.range n).foldl (fun acc i => acc + numeratorBound (a i 0)) 0

/-- b=4*C is slower than binary length but satisfies 2^b >= 4*C. -/
def precision (a : CoefficientNames) (n t : Nat) : Nat :=
  let R := nameBound a n + 2
  n * (t + 2) + 4 * n * R ^ (n - 1)

def sampleMonic (a : CoefficientNames) (n s : Nat) : Poly :=
  (List.range n).map (fun i => a i s) ++ [one]

def rootSupport (root : RootEngine) (a : CoefficientNames)
    (n t : Nat) : List GQ :=
  let s := precision a n t
  approximateFactor root (sampleMonic a n s) (dyadic s)

/-- UNPROVED root-support coherence proposition. -/
def RootSupportCoherenceTarget : Prop :=
  ∀ root, ApproxRootSpec root → ∀ a n,
    0 < n → FastCoefficients a n → ∀ t u, t ≤ u →
    close (rootSupport root a n t) (rootSupport root a n u)
      (dyadic (t + 2)) = true

/-! ## Concrete point names and rational adequacy clauses

There is no host `Real` or `Complex` in this interface. `ZeroAtName` is the
explicit normalized vanishing-residual formulation of P(z)=0. Membership
asks for a finite rational sample within a prescribed radius of a finite
root list. The sample error adds at most the same radius. With the regular
name assumptions this is equivalent to zero distance from the represented
root support, as proved on paper.
-/

abbrev PointName := Nat → GQ

def FastPoint (z : PointName) : Prop :=
  ∀ s t, normSq (sub (z s) (z t)) ≤ (dyadic s + dyadic t) ^ 2

/-- Sample formulation of the supplied represented bound |z| <= Z. -/
def PointBound (z : PointName) (Z : Nat) : Prop :=
  ∀ s, normSq (z s) ≤ ((Z : Rat) + dyadic s) ^ 2

def sampleEvaluation (a : CoefficientNames) (n : Nat)
    (z : PointName) (s : Nat) : GQ :=
  eval (sampleMonic a n s) (z s)

def coefficientEvaluationBound (n U : Nat) : Rat :=
  (n : Rat) * (U : Rat) ^ (n - 1)

def polynomialLipschitzBound (a : CoefficientNames) (n U : Nat) : Rat :=
  (nameBound a n : Rat) *
    (List.range n).foldl
      (fun acc i => acc + ((i + 1 : Nat) : Rat) * (U : Rat) ^ i) 0

def evaluationErrorBound (a : CoefficientNames) (n Z : Nat) : Rat :=
  coefficientEvaluationBound n (Z + 1) +
    polynomialLipschitzBound a n (Z + 1)

def ZeroAtName (a : CoefficientNames) (n : Nat)
    (z : PointName) (Z : Nat) : Prop :=
  ∀ s, normSq (sampleEvaluation a n z s) ≤
    (evaluationErrorBound a n Z * dyadic s) ^ 2

def SampledMember (root : RootEngine) (a : CoefficientNames)
    (n : Nat) (z : PointName) : Prop :=
  ∀ k, ∃ t s, k ≤ t ∧ k + 1 ≤ s ∧
    cover [z s] (rootSupport root a n t) (dyadic (k + 1)) = true

/-- A generous PR exponent ell(v) with 2^ell(v) >= max(1,v). -/
def powerBudget (v : Rat) : Nat := 1 + v.num.natAbs

def adequacySetIndex (n Z k : Nat) : Nat :=
  k + 1 + powerBudget (2 * coefficientEvaluationBound n (Z + 1))

def adequacyPointIndex (a : CoefficientNames) (n Z k : Nat) : Nat :=
  max (k + 1)
    (n * (k + 3) + powerBudget
      (coefficientEvaluationBound n (Z + 1) + evaluationErrorBound a n Z))

/--
UNPROVED quantified finite-precision version of root-to-membership.
The two indices are explicit; the only existential search is the bounded
`cover` check on the finite output list.
-/
def RootToSampledMemberTarget : Prop :=
  ∀ root, ApproxRootSpec root → ∀ a n z Z,
    0 < n → FastCoefficients a n → FastPoint z →
    nameBound a n + 2 ≤ Z → PointBound z Z → ZeroAtName a n z Z →
    ∀ k,
      let t := adequacySetIndex n Z k
      let s := adequacyPointIndex a n Z k
      k ≤ t ∧ k + 1 ≤ s ∧
        cover [z s] (rootSupport root a n t) (dyadic (k + 1)) = true

/--
UNPROVED adequacy equivalence in rational samples only. For the converse,
first bound evaluations at the supplied nearby samples, then compare to
any fixed sample using the regular-name estimate, and remove rational
slack. No real-minimum selector or unbounded computational search occurs.
-/
def SampledRootAdequacyTarget : Prop :=
  ∀ root, ApproxRootSpec root → ∀ a n z Z,
    0 < n → FastCoefficients a n → FastPoint z →
    nameBound a n + 2 ≤ Z → PointBound z Z →
    (ZeroAtName a n z Z ↔ SampledMember root a n z)

-- One finite closed computation; this does not prove any named target.
#eval close [zero, zero] [zero] 0

end IPRADemand.RootSets
