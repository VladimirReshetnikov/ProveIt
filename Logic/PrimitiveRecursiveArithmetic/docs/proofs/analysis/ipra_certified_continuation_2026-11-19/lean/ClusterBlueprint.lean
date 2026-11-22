/-!
# Finite cluster transport: definitions and explicit proof goals

STATUS: UNCOMPILED BLUEPRINT. This file gives executable native Lean
definitions and named `Prop` specifications. A definition ending in `Goal`
does not prove the proposition it defines. No completed ordinary-iPRA
derivation is claimed here.

All graph sizes, table entries, multiplicities and dimensions below are
numerical data. `leastAccepted` is a finite recursion, and its uses in the
graph selectors close it over concrete Boolean predicates. It is not a
universal evaluator for arbitrary primitive-recursive program codes.

The corresponding object-theory port must encode these finite values as
natural numbers, construct the actual PR symbols, prove their evaluation
equations, reflect the bounded predicates, and return `Prf PRAAx` values.
The augmenting-path proof in the report supplies the mathematical existence
argument; the simpler bounded exhaustive selector here can use that result.

For root applications, a root-counting/coverage producer must justify the
common multiplicity data. Rational occurrence points below provide one
concrete finite interface, not an evaluator for arbitrary complex roots.
-/

import Mathlib

namespace IPRAContinuation.ClusterBlueprint

/-! ## Bounded folds and bit encodings -/

def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  (List.range n).all f

def anyBelow (n : Nat) (f : Nat → Bool) : Bool :=
  (List.range n).any f

def sumBelowNat (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + f i) 0

def sumBelowRat (n : Nat) (f : Nat → ℚ) : ℚ :=
  (List.range n).foldl (fun acc i => acc + f i) 0

def bit (code i : Nat) : Bool :=
  ((code / 2 ^ i) % 2) == 1

def encodeBits (n : Nat) (f : Nat → Bool) : Nat :=
  sumBelowNat n (fun i => if f i then 2 ^ i else 0)

def popcount (n mask : Nat) : Nat :=
  sumBelowNat n (fun i => if bit mask i then 1 else 0)

structure Graph where
  size : Nat
  code : Nat
  deriving Repr

def GraphShape (n e : Nat) : Prop :=
  e < 2 ^ (n * n)

def edge (n e i j : Nat) : Bool :=
  bit e (i * n + j)

def encodeGraph (n : Nat) (adjacent : Nat → Nat → Bool) : Nat :=
  encodeBits (n * n) (fun k => adjacent (k / n) (k % n))

def neighborBit (n e mask j : Nat) : Bool :=
  anyBelow n (fun i => bit mask i && edge n e i j)

def neighborMask (n e mask : Nat) : Nat :=
  encodeBits n (neighborBit n e mask)

def Hall (n e : Nat) : Prop :=
  ∀ mask < 2 ^ n,
    popcount n mask ≤ popcount n (neighborMask n e mask)

def DefectSpec (n e mask : Nat) : Prop :=
  mask < 2 ^ n ∧
    popcount n (neighborMask n e mask) < popcount n mask

def defectB (n e mask : Nat) : Bool :=
  decide (mask < 2 ^ n) &&
    decide (popcount n (neighborMask n e mask) < popcount n mask)

/-! ## Permutation codes and an actual bounded selector -/

/-- Exactly N digits, each in a base N+1 alphabet; digit N is disallowed
    by the matching checker. For N=0 the sole bounded code is 0. -/
def permutationCap (n : Nat) : Nat :=
  (n + 1) ^ n

def permutationDigit (n p i : Nat) : Nat :=
  (p / (n + 1) ^ i) % (n + 1)

def MatchingSpec (n e p : Nat) : Prop :=
  p < permutationCap n ∧
    (∀ i < n,
      permutationDigit n p i < n ∧
        edge n e i (permutationDigit n p i) = true) ∧
    (∀ i < n, ∀ j < n,
      permutationDigit n p i = permutationDigit n p j → i = j)

def matchingB (n e p : Nat) : Bool :=
  decide (p < permutationCap n) &&
    allBelow n (fun i =>
      decide (permutationDigit n p i < n) &&
        edge n e i (permutationDigit n p i) &&
        allBelow n (fun j =>
          decide (permutationDigit n p i ≠ permutationDigit n p j) ||
            decide (i = j)))

/-- Ascending bounded search, defined by primitive recursion on the bound.
    It returns the least accepted input below the bound, or `none`. -/
def leastAccepted (accepts : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | Nat.succ k =>
      match leastAccepted accepts k with
      | some i => some i
      | none => if accepts k then some k else none

def selectMatching (n e : Nat) : Option Nat :=
  leastAccepted (matchingB n e) (permutationCap n)

def selectDefect (n e : Nat) : Option Nat :=
  leastAccepted (defectB n e) (2 ^ n)

inductive Decision where
  | matching (permutationCode : Nat)
  | defect (subsetMask : Nat)
  | failed
  deriving Repr

def decideGraph (n e : Nat) : Decision :=
  match selectMatching n e with
  | some p => .matching p
  | none =>
      match selectDefect n e with
      | some mask => .defect mask
      | none => .failed

def DecisionCorrect (n e : Nat) : Decision → Prop
  | .matching p => MatchingSpec n e p
  | .defect mask => DefectSpec n e mask
  | .failed => False

/-- Reflection of the concrete bounded matching checker. -/
def matchingReflectionGoal : Prop :=
  ∀ n e p, matchingB n e p = true ↔ MatchingSpec n e p

def defectReflectionGoal : Prop :=
  ∀ n e mask, defectB n e mask = true ↔ DefectSpec n e mask

/-- This is an external native schema. The object port uses fixed PR
    instances, including precisely the two graph predicates above. -/
def leastAcceptedSpecificationGoal : Prop :=
  ∀ (accepts : Nat → Bool) bound,
    match leastAccepted accepts bound with
    | some i =>
        i < bound ∧ accepts i = true ∧
          ∀ j < i, accepts j = false
    | none => ∀ i < bound, accepts i = false

/-- The main finite graph theorem, including the empty graph. -/
def matchingOrHallDefectGoal : Prop :=
  ∀ n e, GraphShape n e → DecisionCorrect n e (decideGraph n e)

def hallEquivalenceGoal : Prop :=
  ∀ n e, GraphShape n e →
    (Hall n e ↔ ∃ p, MatchingSpec n e p)

/-- If Hall holds, the actual bounded selector returns its least code. -/
def hallSelectsMatchingGoal : Prop :=
  ∀ n e, GraphShape n e → Hall n e →
    ∃ p,
      selectMatching n e = some p ∧
      MatchingSpec n e p ∧
      ∀ q < p, matchingB n e q = false

/-! ## Rational points, weighted families and common occurrence covers -/

abbrev Point := List ℚ

def coordinate (x : Point) (i : Nat) : ℚ :=
  x.getD i 0

def pointAt (xs : List Point) (i : Nat) : Point :=
  xs.getD i []

def ratAbs (x : ℚ) : ℚ :=
  if x < 0 then -x else x

/-- A bounded rational metric on length-d point codes. Invalid lengths
    are totalized by zero coordinates and get no theorem without guards. -/
def l1Distance (d : Nat) (x y : Point) : ℚ :=
  sumBelowRat d (fun i => ratAbs (coordinate x i - coordinate y i))

structure WeightedFamily where
  dimension : Nat
  centers : List Point
  weights : List Nat
  deriving Repr

def centerAt (a : WeightedFamily) (i : Nat) : Point :=
  pointAt a.centers i

def weightAt (a : WeightedFamily) (i : Nat) : Nat :=
  a.weights.getD i 0

def totalWeight (a : WeightedFamily) : Nat :=
  a.weights.foldl (· + ·) 0

def familyShapeB (a : WeightedFamily) : Bool :=
  decide (a.centers.length = a.weights.length) &&
    a.centers.all (fun x => decide (x.length = a.dimension)) &&
    a.weights.all (fun w => decide (0 < w))

def expandedCenters (a : WeightedFamily) : List Point :=
  (List.range a.centers.length).flatMap
    (fun i => List.replicate (weightAt a i) (centerAt a i))

def labelAt (labels : List Nat) (t : Nat) : Nat :=
  labels.getD t 0

def labelCount (occurrences : Nat) (labels : List Nat) (i : Nat) : Nat :=
  sumBelowNat occurrences (fun t => if labelAt labels t == i then 1 else 0)

/-- A complete finite count table: every occurrence has an in-range label
    and each declared weight is its actual number of occurrences. -/
def countCoverB (occurrences : Nat) (a : WeightedFamily)
    (labels : List Nat) : Bool :=
  familyShapeB a &&
    decide (labels.length = occurrences) &&
    allBelow occurrences (fun t =>
      decide (labelAt labels t < a.centers.length)) &&
    allBelow a.centers.length (fun i =>
      decide (labelCount occurrences labels i = weightAt a i))

/-- A complete enclosure of the displayed rational occurrence list.
    The list may have repetitions: multiplicity is counted by positions. -/
def rationalCoverB (points : List Point) (a : WeightedFamily)
    (labels : List Nat) (radius : ℚ) : Bool :=
  countCoverB points.length a labels &&
    decide (0 ≤ radius) &&
    points.all (fun x => decide (x.length = a.dimension)) &&
    allBelow points.length (fun t =>
      decide (l1Distance a.dimension (pointAt points t)
        (centerAt a (labelAt labels t)) ≤ radius))

structure CommonOccurrenceLabels where
  occurrenceCount : Nat
  leftLabels : List Nat
  rightLabels : List Nat
  deriving Repr

/-- This finite interface can be derived from geometric coverage.
    It records counts and one local proximity edge per occurrence,
    not a matching of the public expanded slot lists. -/
def commonIncidenceCoverB (a b : WeightedFamily)
    (w : CommonOccurrenceLabels) (delta : ℚ) : Bool :=
  decide (a.dimension = b.dimension) &&
    decide (0 ≤ delta) &&
    countCoverB w.occurrenceCount a w.leftLabels &&
    countCoverB w.occurrenceCount b w.rightLabels &&
    allBelow w.occurrenceCount (fun t =>
      decide (l1Distance a.dimension
        (centerAt a (labelAt w.leftLabels t))
        (centerAt b (labelAt w.rightLabels t)) ≤ delta))

/-- This public graph depends only on centers, weights and delta. -/
def expandedProximityGraph (a b : WeightedFamily) (delta : ℚ) : Graph :=
  let n := totalWeight a
  let xs := expandedCenters a
  let ys := expandedCenters b
  { size := n
    code := encodeGraph n (fun i j =>
      decide (l1Distance a.dimension (pointAt xs i) (pointAt ys j) ≤ delta)) }

def MatchingDistances (a b : WeightedFamily) (delta : ℚ) (p : Nat) : Prop :=
  let n := totalWeight a
  ∀ i < n,
    l1Distance a.dimension
      (pointAt (expandedCenters a) i)
      (pointAt (expandedCenters b) (permutationDigit n p i)) ≤ delta

/-- The explicit local geometric-to-incidence adapter. -/
def rationalCoversGiveIncidenceGoal : Prop :=
  ∀ (points : List Point) (a b : WeightedFamily)
      (alpha beta : List Nat) (epsilonA epsilonB : ℚ),
    a.dimension = b.dimension →
    rationalCoverB points a alpha epsilonA = true →
    rationalCoverB points b beta epsilonB = true →
    commonIncidenceCoverB a b
      { occurrenceCount := points.length
        leftLabels := alpha
        rightLabels := beta }
      (epsilonA + epsilonB) = true

/-- Count conservation and the actual expanded lengths are conclusions. -/
def coverageCountsGoal : Prop :=
  ∀ occurrences a labels,
    countCoverB occurrences a labels = true →
      totalWeight a = occurrences ∧
      (expandedCenters a).length = occurrences

/-- The main cover-to-Hall step: matching is not a premise. -/
def coverageGivesHallGoal : Prop :=
  ∀ a b w delta,
    commonIncidenceCoverB a b w delta = true →
      let graph := expandedProximityGraph a b delta
      GraphShape graph.size graph.code ∧
      Hall graph.size graph.code

/-- Public bounded selection seals the private occurrence labels. -/
def coverTransportGoal : Prop :=
  ∀ a b w delta,
    commonIncidenceCoverB a b w delta = true →
      let graph := expandedProximityGraph a b delta
      ∃ p,
        selectMatching graph.size graph.code = some p ∧
        MatchingSpec graph.size graph.code p ∧
        MatchingDistances a b delta p

/-- Direct rational-geometric specialization of the complete pipeline. -/
def rationalCoverTransportGoal : Prop :=
  ∀ (points : List Point) (a b : WeightedFamily)
      (alpha beta : List Nat) (epsilonA epsilonB : ℚ),
    a.dimension = b.dimension →
    rationalCoverB points a alpha epsilonA = true →
    rationalCoverB points b beta epsilonB = true →
      let graph := expandedProximityGraph a b (epsilonA + epsilonB)
      ∃ p,
        selectMatching graph.size graph.code = some p ∧
        MatchingSpec graph.size graph.code p ∧
        MatchingDistances a b (epsilonA + epsilonB) p

/-! ## Stable locator labels -/

def singletonFamily (d : Nat) (centers : List Point) : WeightedFamily :=
  { dimension := d
    centers := centers
    weights := List.replicate centers.length 1 }

structure LocatorCertificate where
  dimension : Nat
  anchors : List Point
  occurrenceOwners : List Nat
  radius : ℚ
  gap : ℚ
  deriving Repr

/-- One occurrence per anchor, complete coverage, and a positive gap. -/
def locatorCertificateB (points : List Point) (c : LocatorCertificate) : Bool :=
  rationalCoverB points (singletonFamily c.dimension c.anchors)
    c.occurrenceOwners c.radius &&
    decide (0 < c.gap) &&
    allBelow c.anchors.length (fun i =>
      allBelow c.anchors.length (fun j =>
        decide (i = j) ||
        decide (2 * c.radius + c.gap ≤
          l1Distance c.dimension (pointAt c.anchors i) (pointAt c.anchors j))))

/-- Lowest index minimizing the exact rational distance.
    With no anchors the default is 0; no nonempty-cover guarantee then applies. -/
def nearestAnchor (d : Nat) (anchors : List Point) (x : Point) : Nat :=
  (List.range anchors.length).foldl
    (fun best j =>
      if l1Distance d x (pointAt anchors j) <
          l1Distance d x (pointAt anchors best)
      then j else best)
    0

def sampleLabel (c : LocatorCertificate) (samples : List Point) (i : Nat) : Nat :=
  nearestAnchor c.dimension c.anchors (pointAt samples i)

def singletonSampleCoverB (points samples : List Point) (d : Nat)
    (occurrenceToSample : List Nat) (epsilon : ℚ) : Bool :=
  rationalCoverB points (singletonFamily d samples) occurrenceToSample epsilon

def LabelsBijection (c : LocatorCertificate) (samples : List Point) : Prop :=
  (∀ i < samples.length, sampleLabel c samples i < c.anchors.length) ∧
  (∀ i < samples.length, ∀ j < samples.length,
    sampleLabel c samples i = sampleLabel c samples j → i = j) ∧
  (∀ j < c.anchors.length,
    ∃ i < samples.length, sampleLabel c samples i = j)

/-- The stronger occurrence-indexed statement identifies exactly which
    occurrence each public label denotes. Numeric approximants may differ. -/
def locatorLabelsGoal : Prop :=
  ∀ (points samples : List Point) (c : LocatorCertificate)
      (occurrenceToSample : List Nat) (epsilon : ℚ),
    locatorCertificateB points c = true →
    singletonSampleCoverB points samples c.dimension
      occurrenceToSample epsilon = true →
    epsilon ≤ c.gap / 4 →
      LabelsBijection c samples ∧
      ∀ t < points.length,
        sampleLabel c samples (labelAt occurrenceToSample t) =
          labelAt c.occurrenceOwners t

def locatorCrossPrecisionGoal : Prop :=
  ∀ (points samplesA samplesB : List Point) (c : LocatorCertificate)
      (toA toB : List Nat) (epsilonA epsilonB : ℚ),
    locatorCertificateB points c = true →
    singletonSampleCoverB points samplesA c.dimension toA epsilonA = true →
    singletonSampleCoverB points samplesB c.dimension toB epsilonB = true →
    epsilonA ≤ c.gap / 4 → epsilonB ≤ c.gap / 4 →
      ∀ i < samplesA.length, ∀ j < samplesB.length,
        sampleLabel c samplesA i = sampleLabel c samplesB j →
          l1Distance c.dimension (pointAt samplesA i) (pointAt samplesB j) ≤
            epsilonA + epsilonB

/-! ## Object-theory implementation order

1. Port bit/array encoding, prove encode/decode and bounded population counts.
2. Port `matchingB`, `defectB`, and `leastAccepted`, including actual PR codes.
3. Prove the finite augmenting-path matching-or-defect lemma using the report's
   bounded search invariants. Combine it with the exhaustive-selector
   specification to prove `matchingOrHallDefectGoal` for the actual selector.
4. Derive `coverageCountsGoal` and `coverageGivesHallGoal` from the actual
   count tables; then derive `coverTransportGoal` by ordinary proof composition.
5. Prove rational l1 triangle inequalities and `rationalCoversGiveIncidenceGoal`.
6. Prove the bounded minimum scan, strict locator comparison, labels and their
   cross-precision bound. No real equality test is used.
7. Translate each fixed bounded predicate with the existing `BoundedSyntax`
   frontend. Prove all loop invariants as Boolean equations, not induction on
   unbounded assertions. Publish the resulting ordinary `Prf PRAAx` sequents.

No symbolic theorem-code evaluator or blanket reflection principle is part of
this blueprint. A concrete polynomial root-count producer is still needed to
instantiate its common-occurrence interface for non-rational roots.
-/

end IPRAContinuation.ClusterBlueprint
