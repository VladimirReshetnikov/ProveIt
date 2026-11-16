import Std

/-!
# Explicit semantic targets for the research manuscript

STATUS: This file defines data and pending proof obligations. Lean type-checks
these interfaces; it does not prove that the `Spec` structures are inhabited
or that the `Goal` propositions hold. No theorem in this file is advertised as
an object-language iPRA derivation.

The arithmetic uses only `Rat`, natural numbers, and finite lists. A function
field such as `sample : Nat → Rat` is an AMBIENT Lean parameter. Its primitive
recursive definability, its concrete PR syntax, the Boolean reflection of its
finite contracts, and an actual `Prf PRAAx [] ...` derivation are separate
formalization obligations. In the object theory each such evaluator is fixed;
the targets do not authorize a universal evaluator for arbitrary PR codes.
-/

namespace FiniteObservation.Targets

abbrev Q := Rat
abbrev ScalarSampler := Nat → Q
abbrev Point := List Q

def absQ (x : Q) : Q := x.abs
def eps (k : Nat) : Q := 1 / (2 : Q) ^ k

def RegularScalarGoal (a : ScalarSampler) : Prop :=
  ∀ p q, absQ (a p - a q) ≤ eps p + eps q

/-- Equality and order of regular names, expressed only through rational rows. -/
def EqualScalarGoal (a b : ScalarSampler) : Prop :=
  ∀ p q, absQ (a p - b q) ≤ eps p + eps q

def LeScalarGoal (a b : ScalarSampler) : Prop :=
  ∀ p q, a p ≤ b q + eps p + eps q

def addConstant (a : ScalarSampler) (c : Q) : ScalarSampler := fun p => a p + c

def pointEntry (x : Point) (i : Nat) : Q := x[i]?.getD 0

def cubeDistance (d : Nat) (x y : Point) : Q :=
  (List.range d).foldl
    (fun m i => max m (absQ (pointEntry x i - pointEntry y i))) 0

def InCubeGoal (d : Nat) (x : Point) : Prop :=
  x.length = d ∧ ∀ a, a ∈ x → 0 ≤ a ∧ a ≤ 1

def RegularPointGoal (d : Nat) (x : Nat → Point) : Prop :=
  ∀ p q, cubeDistance d (x p) (x q) ≤ eps p + eps q

def EqualPointGoal (d : Nat) (x y : Nat → Point) : Prop :=
  ∀ p q, cubeDistance d (x p) (y q) ≤ eps p + eps q

structure PointNameSpec (d : Nat) where
  sample : Nat → Point
  inCube : ∀ p, InCubeGoal d (sample p)
  regular : RegularPointGoal d sample

/-- Assumptions for the finite-net theorem, not a completed construction. -/
structure ScalarPresentationSpec (d : Nat) where
  sample : Point → Nat → Q
  modulus : Nat → Nat
  regular : ∀ x, InCubeGoal d x → RegularScalarGoal (sample x)
  continuity : ∀ x y k p q,
    InCubeGoal d x → InCubeGoal d y →
    cubeDistance d x y ≤ eps (modulus k) →
    absQ (sample x p - sample y q) ≤ eps k + eps p + eps q

def intervalCenter (lower upper : Nat → Q) : ScalarSampler :=
  fun p => (lower p + upper p) / 2

/-- Every proof-valued field below is an outstanding formalization obligation. -/
structure FiniteNetInfimumSpec {d : Nat} (F : ScalarPresentationSpec d) where
  approx : Nat → Point
  lower : Nat → Q
  upper : Nat → Q
  approxInCube : ∀ k, InCubeGoal d (approx k)
  nonempty : ∀ k, lower k ≤ upper k
  nestedLower : ∀ k, lower k ≤ lower (k + 1)
  nestedUpper : ∀ k, upper (k + 1) ≤ upper k
  width : ∀ k, upper k - lower k ≤ (3 : Q) / 4 * eps k
  lowerBound : ∀ k x q, InCubeGoal d x → lower k ≤ F.sample x q + eps q
  /-- The current grid minimizer need not realize the running upper endpoint. -/
  finiteApproximation : ∀ k q,
    F.sample (approx k) q ≤ lower k + (3 : Q) / 4 * eps k + eps q
  regularValue : RegularScalarGoal (intervalCenter lower upper)
  valueLowerBound : ∀ x, InCubeGoal d x →
    LeScalarGoal (intervalCenter lower upper) (F.sample x)
  approximateAttainment : ∀ k,
    LeScalarGoal (F.sample (approx k))
      (addConstant (intervalCenter lower upper) ((3 : Q) / 4 * eps k))

def FiniteNetInfimumGoal : Prop :=
  ∀ d (F : ScalarPresentationSpec d), Nonempty (FiniteNetInfimumSpec F)

/-- A monotone numerical majorant. Its input is one fixed evaluator. -/
def maxThrough (f : Nat → Nat) (k : Nat) : Nat :=
  (List.range (k + 1)).foldl (fun m j => max m (f j)) 0

/-- The extra shift accommodates the two-error regular-point convention. -/
def canonicalRead (mu : Nat → Nat) (p : Nat) : Nat :=
  p + 3 + maxThrough mu (p + 3)

def canonicalValue {d : Nat} (F : ScalarPresentationSpec d)
    (x : Nat → Point) : ScalarSampler :=
  fun p => F.sample (x (canonicalRead F.modulus p)) (p + 3)

structure QuantitativeUniquenessSpec {d : Nat} (F : ScalarPresentationSpec d)
    (V : ScalarSampler) where
  cutoff : Nat → Nat
  isolates : ∀ k x y,
    InCubeGoal d x → InCubeGoal d y →
    LeScalarGoal (F.sample x) (addConstant V (eps (cutoff k))) →
    LeScalarGoal (F.sample y) (addConstant V (eps (cutoff k))) →
    cubeDistance d x y ≤ eps k

structure CoherentMinimizerSpec {d : Nat} (F : ScalarPresentationSpec d)
    (V : ScalarSampler) where
  point : PointNameSpec d
  regularValue : RegularScalarGoal (canonicalValue F point.sample)
  optimal : EqualScalarGoal (canonicalValue F point.sample) V
  unique : ∀ other : PointNameSpec d,
    EqualScalarGoal (canonicalValue F other.sample) V →
    EqualPointGoal d point.sample other.sample

def CoherentMinimizerGoal : Prop :=
  ∀ d (F : ScalarPresentationSpec d) (I : FiniteNetInfimumSpec F),
    Nonempty (QuantitativeUniquenessSpec F (intervalCenter I.lower I.upper)) →
    Nonempty (CoherentMinimizerSpec F (intervalCenter I.lower I.upper))

def midpoint (x y : Point) : Point :=
  (x.zip y).map (fun z => (z.1 + z.2) / 2)

structure MidpointStrongConvexitySpec {d : Nat} (F : ScalarPresentationSpec d) where
  constant : Q
  positive : 0 < constant
  midpointDrop : ∀ x y p q r,
    InCubeGoal d x → InCubeGoal d y →
    F.sample (midpoint x y) p ≤
      (F.sample x q + F.sample y r) / 2 -
        constant / 8 * cubeDistance d x y ^ 2 + eps p + (eps q + eps r) / 2

def StrongConvexMinimizerGoal : Prop :=
  ∀ d (F : ScalarPresentationSpec d) (I : FiniteNetInfimumSpec F),
    Nonempty (MidpointStrongConvexitySpec F) →
    Nonempty (CoherentMinimizerSpec F (intervalCenter I.lower I.upper))

/-! ## Rationally presented positive convex functions -/

structure PositiveRationalPresentationSpec where
  sample : Q → Nat → Q
  regular : ∀ x, 0 < x → RegularScalarGoal (sample x)
  /-- This finite quantitative witness is data, not extracted from `¬ (F x = 0)`. -/
  positiveMargin : Q → Q
  marginPositive : ∀ x, 0 < x → 0 < positiveMargin x
  marginValid : ∀ x p, 0 < x → positiveMargin x ≤ sample x p + eps p

def rationalCombination (x y : Q) (s j : Nat) : Q :=
  (((s - j : Nat) : Q) * x + (j : Q) * y) / (s : Q)

/-- Numerical reading schedule for rational multiplicative convexity.
    The powers use a common finite source row; they are not silently treated
    as already normalized regular names. -/
structure MultiplicativeConvexSpec (F : PositiveRationalPresentationSpec) where
  read : Q → Q → Nat → Nat → Nat → Nat
  readLarge : ∀ x y s j k, k ≤ read x y s j k
  finiteInequality : ∀ x y s j k,
    0 < x → 0 < y → 0 < s → j ≤ s →
    let p := read x y s j k
    F.sample (rationalCombination x y s j) p ^ s ≤
      F.sample x p ^ (s - j) * F.sample y p ^ j + eps k

def endpointUpper (F : PositiveRationalPresentationSpec) (alpha beta : Q) : Nat :=
  1 + (max (absQ (F.sample (alpha / 2) 0))
           (absQ (F.sample (beta + 1) 0))).ceil.toNat

def endpointDelta (alpha : Q) : Q := min (alpha / 2) 1

def endpointSlope (F : PositiveRationalPresentationSpec) (alpha beta : Q) : Nat :=
  (((endpointUpper F alpha beta : Nat) : Q) / endpointDelta alpha).ceil.toNat

def derivedLocalModulus (F : PositiveRationalPresentationSpec)
    (alpha beta : Q) (k : Nat) : Nat :=
  k + endpointSlope F alpha beta

def ConvexLipschitzGoal (F : PositiveRationalPresentationSpec) : Prop :=
  ∀ alpha beta x y p q,
    0 < alpha → alpha ≤ beta →
    alpha ≤ x → x ≤ beta → alpha ≤ y → y ≤ beta →
    absQ (F.sample x p - F.sample y q) ≤
      ((endpointUpper F alpha beta : Nat) : Q) / endpointDelta alpha *
        absQ (x - y) + eps p + eps q

def DerivedLocalModulusGoal (F : PositiveRationalPresentationSpec) : Prop :=
  ∀ alpha beta x y k p q,
    0 < alpha → alpha ≤ beta →
    alpha ≤ x → x ≤ beta → alpha ≤ y → y ≤ beta →
    absQ (x - y) ≤ eps (derivedLocalModulus F alpha beta k) →
    absQ (F.sample x p - F.sample y q) ≤ eps k + eps p + eps q

def ConvexModulusRepairGoal : Prop :=
  ∀ F : PositiveRationalPresentationSpec,
    Nonempty (MultiplicativeConvexSpec F) →
    ConvexLipschitzGoal F ∧ DerivedLocalModulusGoal F

/-! ## Rational polynomial sections -/

abbrev QPoly := List Q

def qCoeff (f : QPoly) (i : Nat) : Q := f[i]?.getD 0

def qEval (f : QPoly) (x : Q) : Q :=
  f.foldr (fun a r => a + x * r) 0

/-- `none` denotes the zero polynomial; trailing zero coefficients are ignored. -/
def qDegree (f : QPoly) : Option Nat :=
  (List.range f.length).foldl
    (fun old i => if qCoeff f i = 0 then old else some i) none

structure QPoint where
  x : Q
  y : Q
  deriving DecidableEq, Repr

def onCurve (f : QPoly) (r : Nat) (p : QPoint) : Prop :=
  p.y ^ r = qEval f p.x

def features (s : Nat) (p : QPoint) : List Q :=
  (List.range (s + 1)).map (fun j => p.x ^ j) ++ [p.y]

def dotQ (x y : List Q) : Q :=
  (x.zip y).foldl (fun acc z => acc + z.1 * z.2) 0

def nonzeroVector (x : List Q) : Bool := x.any (fun a => decide (a ≠ 0))

def annihilates (s : Nat) (lambda : List Q) (p : QPoint) : Prop :=
  dotQ lambda (features s p) = 0

def PolynomialRootCountGoal : Prop :=
  ∀ (f : QPoly) (D : Nat) (roots : List Q),
    qDegree f = some D → roots.Nodup →
    (∀ x, x ∈ roots → qEval f x = 0) → roots.length ≤ D

def SuperellipticSectionGoal : Prop :=
  ∀ (f : QPoly) (r s m : Nat) (lambda : List Q) (points : List QPoint),
    0 < r → qDegree f = some m → r * s < m →
    lambda.length = s + 2 → nonzeroVector lambda = true →
    points.Nodup →
    (∀ p, p ∈ points → onCurve f r p ∧ annihilates s lambda p) →
    points.length ≤ m

/-- A supplied finite cover. Its existence is a separate mathematical input. -/
structure HyperplaneCoverSpec (s : Nat) (points : List QPoint) where
  planes : List (List Q)
  valid : ∀ l, l ∈ planes → l.length = s + 2 ∧ nonzeroVector l = true
  covers : ∀ p, p ∈ points → ∃ l, l ∈ planes ∧ annihilates s l p

def SuperellipticCoverGoal : Prop :=
  ∀ (f : QPoly) (r s m : Nat) (points : List QPoint)
      (cover : HyperplaneCoverSpec s points),
    0 < r → qDegree f = some m → r * s < m →
    points.Nodup → (∀ p, p ∈ points → onCurve f r p) →
    points.length ≤ m * cover.planes.length

/-! ## Gaussian-rational coefficient names and uniform factorization -/

structure GQ where
  re : Q
  im : Q
  deriving DecidableEq, Repr

def gZero : GQ := ⟨0, 0⟩
def gOne : GQ := ⟨1, 0⟩
def gAdd (a b : GQ) : GQ := ⟨a.re + b.re, a.im + b.im⟩
def gNeg (a : GQ) : GQ := ⟨-a.re, -a.im⟩
def gSub (a b : GQ) : GQ := gAdd a (gNeg b)
def gMul (a b : GQ) : GQ :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def gNorm (a : GQ) : Q := absQ a.re + absQ a.im

abbrev GPoly := List GQ
abbrev CoefficientSampler := Nat → Nat → GQ

def gCoeff (p : GPoly) (i : Nat) : GQ := p[i]?.getD gZero

def gPolySub (p q : GPoly) : GPoly :=
  (List.range (max p.length q.length)).map
    (fun i => gSub (gCoeff p i) (gCoeff q i))

/-- The extra trailing zero is harmless; all target norms include it. -/
def gPolyMul (p q : GPoly) : GPoly :=
  (List.range (p.length + q.length)).map fun k =>
    (List.range (k + 1)).foldl
      (fun acc i => gAdd acc (gMul (gCoeff p i) (gCoeff q (k - i)))) gZero

def gPolyNorm (p : GPoly) : Q := p.foldl (fun acc a => acc + gNorm a) 0

def linearProduct (roots : List GQ) : GPoly :=
  roots.foldl (fun p a => gPolyMul p [gNeg a, gOne]) [gOne]

def polynomialRow (a : CoefficientSampler) (d p : Nat) : GPoly :=
  (List.range (d + 1)).map (fun i => a i p)

def RegularGaussianGoal (a : Nat → GQ) : Prop :=
  ∀ p q, gNorm (gSub (a p) (a q)) ≤ eps p + eps q

/-- A finite Booleanizable contract; all quantified indices are bounded. -/
def FiniteCoefficientGoal (d M h : Nat) (a : CoefficientSampler) : Prop :=
  (∀ p, p ≤ h → a d p = gOne) ∧
  (∀ i p, i ≤ d → p ≤ h → gNorm (a i p) ≤ (M : Q)) ∧
  (∀ i p q, i ≤ d → p ≤ h → q ≤ h →
    gNorm (gSub (a i p) (a i q)) ≤ eps p + eps q)

structure MonicCoefficientSpec (d M : Nat) where
  sample : CoefficientSampler
  leading : ∀ p, sample d p = gOne
  bounded : ∀ i p, i ≤ d → gNorm (sample i p) ≤ (M : Q)
  regular : ∀ i, i ≤ d → RegularGaussianGoal (sample i)

/-- The actual evaluator and its verification data remain to be implemented.
    This structure does not itself certify PR definability or iPRA provability. -/
structure NameFactorizationSpec (d M : Nat) (a : MonicCoefficientSpec d M) where
  roots : Nat → Nat → GQ
  shift : Nat
  rootBound : Nat → Nat
  regular : ∀ i, i < d → RegularGaussianGoal (roots i)
  bounded : ∀ i p, i < d → gNorm (roots i p) ≤ (rootBound i : Q)
  productEstimate : ∀ k,
    gPolyNorm
      (gPolySub (polynomialRow a.sample d (k + shift))
        (linearProduct ((List.range d).map (fun i => roots i (k + shift))))) ≤ eps k

def DegreeUniformFactorizationGoal : Prop :=
  ∀ (d M : Nat) (a : MonicCoefficientSpec d M),
    0 < d → 2 ≤ M → Nonempty (NameFactorizationSpec d M a)

/-- Numerical schedules from the manuscript. These are executable definitions;
    no correctness theorem for them is claimed in this specification file. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1
def rootD (n : Nat) : Nat := 2 ^ n * 4 ^ (2 * n * n)
def rootK (n : Nat) : Nat := 8 * n * rootD n
def rootRadius (n M : Nat) : Nat := (M + 2) * rootK n + 1
def rootL (n M : Nat) : Nat :=
  2 + bitLength (16 * rootD n * (n + 1) * rootRadius n M ^ n)
def rootH (n M : Nat) : Nat := bitLength ((M + 2) * rootK n)
def rootQuery (n M p : Nat) : Nat := rootL n M + rootK n * (p + rootH n M + 2)
def rootCap (n M : Nat) : Nat := 2 * rootRadius n M + 1
def deflationE (n M : Nat) : Nat :=
  4 * (n + 1) ^ 2 * (M + 1) * (rootCap n M + 1) ^ (n + 1)
def deflationShift (n M : Nat) : Nat := bitLength (4 * deflationE n M)
def nextCoefficientCap (n M : Nat) : Nat :=
  2 + (n + 1) * (M + 1) * (rootCap n M + 1) ^ n
def deflationDefect (n M : Nat) : Nat :=
  4 * (n + 1) * (nextCoefficientCap n M + 1) * (rootCap n M + 1)
def deflationVerification (n M h : Nat) : Nat :=
  rootQuery n M (h + deflationShift n M + 2)

/-- The pending local theorem that a concrete finite deflation implementation
    must satisfy. The finite input horizon is a VERIFICATION horizon. -/
structure FiniteDeflationSpec (n M : Nat) where
  root : CoefficientSampler → Nat → GQ
  quotient : CoefficientSampler → CoefficientSampler
  prefixStable : ∀ h a b,
    (∀ i p, i ≤ n → p ≤ deflationVerification n M h → a i p = b i p) →
    (∀ p, p ≤ h → root a p = root b p) ∧
    (∀ i p, i < n → p ≤ h → quotient a i p = quotient b i p)
  contract : ∀ a h,
    0 < n → 2 ≤ M →
    FiniteCoefficientGoal n M (deflationVerification n M h) a →
    FiniteCoefficientGoal (n - 1) (nextCoefficientCap n M) h (quotient a) ∧
    (∀ p, p ≤ h → gNorm (root a p) ≤ (rootCap n M : Q)) ∧
    (∀ p q, p ≤ h → q ≤ h →
      gNorm (gSub (root a p) (root a q)) ≤ eps p + eps q) ∧
    (∀ p, p ≤ h →
      gPolyNorm (gPolySub (polynomialRow a n p)
        (gPolyMul [gNeg (root a p), gOne]
          (polynomialRow (quotient a) (n - 1) p))) ≤
        (deflationDefect n M : Q) * eps p)

end FiniteObservation.Targets
