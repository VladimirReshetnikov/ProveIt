import Outline

/-!
# Effective analytic presentations: additional definitions and obligations

STATUS: UNCOMPILED OUTLINE. Every declaration ending in `Goal` is a proposition
to be proved, not a theorem. There are no axioms or placeholder proofs here.

This sibling module assumes `Outline.lean` is importable as `Outline`; when
installing the files under a qualified Lake namespace, update this import.

The structures below are EXTERNAL specifications. A field `Nat → Rat`, or a
universal quantifier over such fields, does not belong to first-order iPRA.
For the arithmetic theorem schema, FIX each sampling program and modulus,
compile its particular PR syntax separately, and translate every use of its
contract into the corresponding first-order assumptions. No universal total
PR interpreter, choice of a limit, or completed real-number type is assumed.
The internal completion target remains `Prf PRAAx [] ...` from Outline.
-/

namespace IsoperimetricAnalytic

open IsoperimetricOutline
open scoped BigOperators

def eps (k : ℕ) : ℚ := 1 / (2 : ℚ)^k

structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

abbrev RawName := ℕ → QInterval

/-- Pairwise compatibility replaces a completeness axiom. -/
def ValidName (x : RawName) : Prop :=
  (∀ k l, (x k).lo ≤ (x l).hi) ∧
  (∀ k, (x k).hi - (x k).lo ≤ eps k)

def boundedRaw (B : ℕ) (x : RawName) : Prop :=
  (∀ k l, (x k).lo ≤ (x l).hi) ∧
  (∀ k, |(x k).lo| ≤ B ∧ |(x k).hi| ≤ B) ∧
  (∀ k, (x k).hi - (x k).lo ≤ (B : ℚ) * eps k)

def pointName (q : ℚ) : RawName := fun _ => ⟨q, q⟩
def nameLE (x y : RawName) : Prop := ∀ k, (x k).lo ≤ (y k).hi
def nameEq (x y : RawName) : Prop := nameLE x y ∧ nameLE y x
def nonnegative (x : RawName) : Prop := nameLE (pointName 0) x

/-- A finite positive-denominator certificate. -/
structure PositiveBound (x : RawName) where
  lower : ℚ
  positive : 0 < lower
  precision : ℕ
  certified : lower ≤ (x precision).lo

def iadd (x y : QInterval) : QInterval := ⟨x.lo + y.lo, x.hi + y.hi⟩
def ineg (x : QInterval) : QInterval := ⟨-x.hi, -x.lo⟩
def imul (x y : QInterval) : QInterval :=
  let a := x.lo * y.lo
  let b := x.lo * y.hi
  let c := x.hi * y.lo
  let d := x.hi * y.hi
  ⟨min (min a b) (min c d), max (max a b) (max c d)⟩
def iabs (x : QInterval) : QInterval :=
  ⟨max 0 (max x.lo (-x.hi)), max |x.lo| |x.hi|⟩
def nadd (x y : RawName) : RawName := fun k => iadd (x k) (y k)
def nneg (x : RawName) : RawName := fun k => ineg (x k)
def nsub (x y : RawName) : RawName := nadd x (nneg y)
def nmul (x y : RawName) : RawName := fun k => imul (x k) (y k)
def nscale (q : ℚ) (x : RawName) : RawName := nmul (pointName q) x
def nabs (x : RawName) : RawName := fun k => iabs (x k)
def npow (x : RawName) : ℕ → RawName
  | 0 => pointName 1
  | n + 1 => nmul (npow x n) x
def nsum (xs : List RawName) : RawName := xs.foldl nadd (pointName 0)
def within (x y : RawName) (e : ℚ) : Prop :=
  nameLE x (nadd y (pointName e)) ∧ nameLE y (nadd x (pointName e))

/- Raw interval arithmetic preserves enclosures but not necessarily the
normalized width eps(k). Its explicit bound and reindexing are obligations;
we deliberately do not install an unsound `ValidName` instance for it. -/

def rootFloor (n B r : ℕ) (x : ℚ) : ℕ :=
  (List.range (2^r * (B + 1) + 1)).foldl
    (fun best j => if (j : ℚ)^n ≤ max 0 x * (2 : ℚ)^(r*n)
                  then j else best) 0

/-- The exact pi-lower algorithm specified in the reused planar paper.
This restricted square-root scan is called only on numbers in [0,1]. -/
def sqrtFloorUnit (x : ℚ) (r : ℕ) : ℚ :=
  (rootFloor 2 2 r x : ℚ) * eps r
def halfCosApprox (r : ℕ) : ℕ → ℚ
  | 0 => 0
  | j+1 => sqrtFloorUnit ((1 + halfCosApprox r j)/2) r
def canonicalPiLower (k : ℕ) : ℚ :=
  let r := k+4
  let t := 4*k+16
  let c := min 1 (halfCosApprox t (r-1) + 2*eps t)
  (2 : ℚ)^r * sqrtFloorUnit (1-c^2) t
def canonicalPiName : RawName := fun k =>
  ⟨canonicalPiLower (k+2), canonicalPiLower (k+2) + eps (k+2)⟩
def CanonicalPiGoal : Prop :=
  ValidName canonicalPiName ∧
  nameLE (pointName 2) canonicalPiName ∧
  nameLE canonicalPiName (pointName 4)

/- Every subsequent pi-parameterized definition is a reusable specification
interface, not a universal theorem for arbitrary RawName values. The actual
theorem targets at the end instantiate canonicalPiName. Its identification
with the dyadic unit-circle perimeter/area is proved in the planar paper and
must be internalized alongside CanonicalPiGoal. Bounds 2 <= pi <= 4 alone
would NOT justify replacing pi by an arbitrary constant. -/

/-- B bounds both endpoint magnitudes and the width multiplier of x. -/
def rootName (n B : ℕ) (x : RawName) : RawName := fun k =>
  let r := k + 2
  let m := n * (k + B + 10)
  ⟨(rootFloor n B r (x m).lo : ℚ) * eps r,
   ((rootFloor n B r (x m).hi : ℚ) + 1) * eps r⟩

def RootGoal : Prop :=
  ∀ n B x, 0 < n → 1 ≤ B → boundedRaw B x → nonnegative x →
    ValidName (rootName n B x) ∧ nonnegative (rootName n B x) ∧
    nameEq (npow (rootName n B x) n) x

structure PolygonalPresentation where
  polygons : ℕ → Polygon
  upperLengths : ℕ → List ℚ
  upperValid : ∀ k, UpperLengths (polygons k) (upperLengths k)
  area : RawName
  length : RawName
  areaValid : ValidName area
  lengthValid : ValidName length
  areaNonnegative : nonnegative area
  lengthNonnegative : nonnegative length
  bound : ℕ
  areaApprox : ∀ k, within (pointName |signedArea (polygons k)|) area (eps k)
  lengthApprox : ∀ k, within (pointName (upperLengths k).sum) length (eps k)
  lengthBound : nameLE length (pointName bound)

/- The region/boundary interpretation additionally requires the report's
compatible Jordan-domain polygon names or its lower-real construction. The
numerical theorem below only needs the displayed area/length contract. -/
def PlanarPresentationGoal (pi : RawName) : Prop :=
  ∀ p : PolygonalPresentation,
    nameLE (nmul (nscale 4 pi) p.area) (npow p.length 2)

def sinTaylor (m : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℚ)^j * x^(2*j+1) / ((2*j+1).factorial : ℚ)
def cosTaylor (m : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℚ)^j * x^(2*j) / ((2*j).factorial : ℚ)
def mid (x : QInterval) : ℚ := (x.lo + x.hi) / 2
def wrap (t : ℚ) : ℚ := t - (⌊t⌋ : ℤ)

/-- Fixed finite approximation to (cos(2*pi*t), sin(2*pi*t)).
Its error theorem requires the actual pi-name from the planar paper. -/
def circleSample (pi : RawName) (t : ℚ) (k : ℕ) : QPoint :=
  let x := 2 * (pi (k + 24)).lo * wrap t
  ⟨cosTaylor (k + 20) x, sinTaylor (k + 20) x⟩

structure SupportPolynomial where
  constant : ℚ
  translation : SupportMode
  higher : List SupportMode
  evaluationBudget : ℕ

def allModes (p : SupportPolynomial) : List SupportMode :=
  p.translation :: p.higher
def coefficientBound (p : SupportPolynomial) : ℚ :=
  |p.constant| + ∑ i ∈ Finset.range (allModes p).length,
    let c := (allModes p).getD i ⟨0,0⟩
    (1 + ((i+1 : ℕ) : ℚ)^2) * (|c.cosine| + |c.sine|)

/-- d=0,1,2 denotes derivative with respect to theta, sampled at theta=2*pi*t. -/
def supportSample (pi : RawName) (p : SupportPolynomial)
    (d : ℕ) (t : ℚ) (k : ℕ) : ℚ :=
  (if d = 0 then p.constant else 0) +
  ∑ i ∈ Finset.range (allModes p).length,
    let c := (allModes p).getD i ⟨0,0⟩
    let n : ℚ := i + 1
    let z := circleSample pi (n*t) (k + p.evaluationBudget + 20)
    if d = 0 then c.cosine*z.x + c.sine*z.y
    else if d = 1 then n*(-c.cosine*z.y + c.sine*z.x)
    else -n^2*(c.cosine*z.x + c.sine*z.y)

def polynomialLength (pi : RawName) (p : SupportPolynomial) : RawName :=
  nscale (2*p.constant) pi
def polynomialArea (pi : RawName) (p : SupportPolynomial) : RawName :=
  nscale (p.constant^2 - supportDeficit p.higher / 2) pi
def polynomialWigner (pi : RawName) (p : SupportPolynomial) : RawName :=
  nscale (-oddSupportDeficit p.higher / 4) pi
def unitParameter (t : ℚ) : Prop := 0 ≤ t ∧ t ≤ 1
def opposite (t : ℚ) : ℚ := if t ≤ 1/2 then t + 1/2 else t - 1/2

structure SupportC2Presentation (pi : RawName) where
  polynomials : ℕ → SupportPolynomial
  coefficientBudgets : ∀ j,
    coefficientBound (polynomials j) ≤ (polynomials j).evaluationBudget
  sample : ℕ → ℚ → ℕ → ℚ
  sampleCauchy : ∀ d t k l, d < 3 → unitParameter t →
    |sample d t k - sample d t l| ≤ eps k + eps l
  approximation : ∀ j d t k, d < 3 → unitParameter t →
    |supportSample pi (polynomials j) d t k - sample d t k|
      ≤ eps j + 2*eps k
  bound : ℕ
  boundPositive : 1 ≤ bound
  uniformBound : ∀ d t k, d < 3 → unitParameter t →
    |sample d t k| ≤ (bound : ℚ) + eps k
  polynomialBound : ∀ j d t k, d < 3 → unitParameter t →
    |supportSample pi (polynomials j) d t k| ≤ (bound : ℚ) + eps k
  radiusLower : ℚ
  radiusPositive : 0 < radiusLower
  radiusLaw : ∀ t k, unitParameter t →
    radiusLower ≤ sample 0 t k + sample 2 t k + 2*eps k
  length : RawName
  area : RawName
  wignerArea : RawName
  quantitiesValid : ValidName length ∧ ValidName area ∧ ValidName wignerArea
  lengthNonnegative : nonnegative length
  areaNonnegative : nonnegative area
  lengthBridge : ∀ j, within (polynomialLength pi (polynomials j)) length (8*eps j)
  areaBridge : ∀ j, within (polynomialArea pi (polynomials j)) area
    (16*(bound : ℚ)*eps j)
  wignerBridge : ∀ j, within (polynomialWigner pi (polynomials j)) wignerArea
    (8*(bound : ℚ)*eps j)

def constantWidth {pi : RawName} (p : SupportC2Presentation pi) : Prop :=
  ∀ t s k, unitParameter t → unitParameter s →
    |p.sample 0 t k + p.sample 0 (opposite t) k -
     p.sample 0 s k - p.sample 0 (opposite s) k| ≤ 4*eps k

def wignerRight {pi : RawName} (p : SupportC2Presentation pi) : RawName :=
  nadd (nmul (nscale 4 pi) p.area) (nmul (nscale 8 pi) (nabs p.wignerArea))
def WignerPresentationGoal (pi : RawName) : Prop :=
  ∀ p : SupportC2Presentation pi,
    nameLE (wignerRight p) (npow p.length 2) ∧
    (nameEq (npow p.length 2) (wignerRight p) ↔ constantWidth p)

def boxMember {d : ℕ} (b : QBox d) (x : Fin d → ℚ) : Prop :=
  ∀ i, b.lo i ≤ x i ∧ x i ≤ b.hi i
def unionMember {d : ℕ} (bs : BoxUnion d) (x : Fin d → ℚ) : Prop :=
  ∃ b ∈ bs, boxMember b x
def qSubset {d : ℕ} (x y : BoxUnion d) : Prop :=
  ∀ z : Fin d → ℚ, unionMember x z → unionMember y z
def scaleBox {d : ℕ} (t : ℚ) (b : QBox d) : QBox d :=
  ⟨fun i => t*b.lo i, fun i => t*b.hi i⟩
def boxSum {d : ℕ} (x y : BoxUnion d) : BoxUnion d :=
  x.flatMap (fun b => y.map (minkowskiBox b))

structure BoxAlgorithms where
  dissect : {d : ℕ} → BoxUnion d → BoxUnion d
  contains : {d : ℕ} → BoxUnion d → BoxUnion d → Bool
def BoxAlgorithmsGoal (a : BoxAlgorithms) : Prop :=
  (∀ d (bs : BoxUnion d), (∀ b ∈ bs, boxValid b) →
    disjointBoxUnion (a.dissect bs) ∧ qSubset bs (a.dissect bs) ∧
      qSubset (a.dissect bs) bs) ∧
  (∀ d (x y : BoxUnion d),
    (∀ b ∈ x, boxValid b) → (∀ b ∈ y, boxValid b) →
    (a.contains x y = true ↔ qSubset x y))

def gridWords (base : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | d+1 => (List.range base).flatMap
      (fun j => (gridWords base d).map (fun w => j :: w))
def unitGrid (d m : ℕ) : BoxUnion d :=
  (gridWords (4*2^m) d).map (fun w =>
    ⟨fun i => (w.getD i.val 0 : ℚ)*eps m - 2,
     fun i => ((w.getD i.val 0 : ℚ)+1)*eps m - 2⟩)
def maxCellNormSq {d : ℕ} (b : QBox d) : ℚ :=
  ∑ i : Fin d, max ((b.lo i)^2) ((b.hi i)^2)
def minCellNormSq {d : ℕ} (b : QBox d) : ℚ :=
  ∑ i : Fin d, if b.hi i < 0 then (b.hi i)^2
    else if 0 < b.lo i then (b.lo i)^2 else 0
def innerBallGrid (d m : ℕ) : BoxUnion d :=
  (unitGrid d m).filter (fun b => decide (maxCellNormSq b ≤ 1))
def outerBallGrid (d m : ℕ) : BoxUnion d :=
  (unitGrid d m).filter (fun b => decide (minCellNormSq b ≤ 1))
def ballMesh (d k : ℕ) : ℕ := k + 3*d^2*4^d + 4*d + 4
def omegaName (d : ℕ) : RawName := fun k =>
  ⟨disjointVolume (innerBallGrid d (ballMesh d k)),
   disjointVolume (outerBallGrid d (ballMesh d k))⟩
def BallGridGoal : Prop := ∀ d, 0 < d →
  ValidName (omegaName d) ∧
  (∀ k, 0 < disjointVolume (innerBallGrid d (ballMesh d k))) ∧
  nameLE (pointName ((2/(d : ℚ))^d)) (omegaName d) ∧
  nameLE (omegaName d) (pointName ((2 : ℚ)^d))

structure OuterVolumePresentation (a : BoxAlgorithms) (d : ℕ) where
  volume : RawName
  perimeter : RawName
  named : ValidName volume ∧ ValidName perimeter
  nonnegativeData : nonnegative volume ∧ nonnegative perimeter
  positiveVolume : PositiveBound volume
  bound : ℕ
  bounded : nameLE volume (pointName bound) ∧ nameLE perimeter (pointName bound)
  inner : ℕ → BoxUnion d
  innerValid : ∀ k, disjointBoxUnion (inner k)
  innerError : ∀ k,
    nameLE (pointName (disjointVolume (inner k))) volume ∧
    nameLE volume (pointName (disjointVolume (inner k) + eps k))
  outer : ℚ → ℕ → BoxUnion d
  outerValid : ∀ t k, 0 < t → disjointBoxUnion (outer t k)
  outerVolume : ℚ → RawName
  outerVolumeValid : ∀ t, 0 < t → ValidName (outerVolume t)
  inclusion : ∀ t k, 0 < t →
    a.contains (boxSum (inner k)
      ((innerBallGrid d (ballMesh d k)).map (scaleBox t))) (outer t k) = true
  outerError : ∀ t k, 0 < t →
    nameLE (pointName (disjointVolume (outer t k)))
      (nadd (outerVolume t) (pointName (eps k)))
  tubeModulus : ℕ → ℕ
  tubeLaw : ∀ j t, 0 < t → t ≤ eps (tubeModulus j) →
    nameLE (outerVolume t)
      (nadd volume (nscale t (nadd perimeter (pointName (eps j)))))

/- Before applying FiniteBMGoal, choose k with eps(k) less than half the
positiveVolume.lower certificate. Pairwise interval compatibility and
innerError imply vol(inner k) >= positiveVolume.lower/2 > 0. BallGridGoal
supplies vol(innerBallGrid d (ballMesh d k)) > 0; scaling by rational t>0
preserves positivity. BOTH BM input volumes are therefore positive. -/

def OuterIsoperimetricGoal (a : BoxAlgorithms) : Prop :=
  BoxAlgorithmsGoal a → ∀ d, 2 ≤ d →
  ∀ p : OuterVolumePresentation a d,
    nameLE (nmul (nscale ((d : ℚ)^d) (omegaName d)) (npow p.volume (d-1)))
      (npow p.perimeter d)

structure LayeredData (d : ℕ) where
  count : ℕ
  level : Fin count → ℚ
  positiveLevels : ∀ i, 0 < level i
  orderedLevels : ∀ i j, i < j → level i < level j
  volume : Fin count → RawName
  perimeter : Fin count → RawName
  valid : ∀ i, ValidName (volume i) ∧ ValidName (perimeter i)
  positiveData : ∀ i, nonnegative (volume i) ∧ nonnegative (perimeter i)
  nestedVolumes : ∀ i j, i < j → nameLE (volume j) (volume i)
  bound : ℕ
  bounds : ∀ i, level i ≤ bound ∧ boundedRaw bound (volume i) ∧
    boundedRaw bound (perimeter i)
  layerIsoperimetry : ∀ i,
    nameLE (nmul (nscale ((d : ℚ)^d) (omegaName d)) (npow (volume i) (d-1)))
      (npow (perimeter i) d)

def layerLevels {d : ℕ} (s : LayeredData d) : List ℚ := List.ofFn s.level
def layerVolumes {d : ℕ} (s : LayeredData d) : List RawName := List.ofFn s.volume
def layerPerimeters {d : ℕ} (s : LayeredData d) : List RawName := List.ofFn s.perimeter
def layerIncrement {d : ℕ} (s : LayeredData d) (j : ℕ) : ℚ :=
  (layerLevels s).getD j 0 - (if j=0 then 0 else (layerLevels s).getD (j-1) 0)
def shellVolume {d : ℕ} (s : LayeredData d) (j : ℕ) : RawName :=
  nsub ((layerVolumes s).getD j (pointName 0))
       ((layerVolumes s).getD (j+1) (pointName 0))
def layerBudget {d : ℕ} (s : LayeredData d) : ℕ :=
  ((s.count+1)*(s.bound+2))^(8*(d+1))
def layerJump {d : ℕ} (s : LayeredData d) : RawName :=
  nsum ((List.range s.count).map (fun j =>
    nscale (layerIncrement s j) ((layerPerimeters s).getD j (pointName 0))))
def layerNorm {d : ℕ} (s : LayeredData d) : RawName :=
  let B := layerBudget s
  let moment := nsum ((List.range s.count).map (fun j =>
    nmul (shellVolume s j)
      (rootName (d-1) B (pointName (((layerLevels s).getD j 0)^d)))))
  rootName d B (npow moment (d-1))
def sobolevFactor (d B : ℕ) : RawName :=
  nscale (d : ℚ) (rootName d B (omegaName d))
def LayeredSobolevGoal : Prop := ∀ d, 2 ≤ d → ∀ s : LayeredData d,
  nameLE (nmul (sobolevFactor d (layerBudget s)) (layerNorm s)) (layerJump s)

structure GridFace where
  area : ℚ
  plusValue : ℚ
  minusValue : ℚ
  areaNonnegative : 0 ≤ area
def faceJump (faces : List GridFace) : ℚ :=
  (faces.map (fun f => f.area * |f.plusValue-f.minusValue|)).sum

def levelFacePerimeter (t : ℚ) (faces : List GridFace) : ℚ :=
  (faces.map (fun f =>
    if min f.plusValue f.minusValue < t ∧ t ≤ max f.plusValue f.minusValue
    then f.area else 0)).sum

/-- A finite numerical incidence contract, constructed from the actual
common-grid interfaces. In geometric applications the face builder must
additionally be checked against cell adjacency and exterior zero values. -/
structure GridCoareaCertificate {d : ℕ} (s : LayeredData d)
    (faces : List GridFace) where
  valuesNonnegative : ∀ f ∈ faces, 0 ≤ f.plusValue ∧ 0 ≤ f.minusValue
  endpointsListed : ∀ f ∈ faces,
    (f.plusValue = 0 ∨ f.plusValue ∈ layerLevels s) ∧
    (f.minusValue = 0 ∨ f.minusValue ∈ layerLevels s)
  perimeterIncidence : ∀ i : Fin s.count,
    nameEq (s.perimeter i) (pointName (levelFacePerimeter (s.level i) faces))

/-- Conditional target for data constructed from one grid function. It is
not an assertion for arbitrary unrelated layered data and arbitrary faces. -/
def GridCoareaGoal {d : ℕ} (s : LayeredData d) (faces : List GridFace) : Prop :=
  GridCoareaCertificate s faces →
  nameEq (layerJump s) (pointName (faceJump faces))

structure SobolevApproximation (d : ℕ) where
  targetNorm : RawName
  gradientIntegral : RawName
  valid : ValidName targetNorm ∧ ValidName gradientIntegral
  nonnegativeData : nonnegative targetNorm ∧ nonnegative gradientIntegral
  layers : ℕ → LayeredData d
  normApprox : ∀ k,
    nameLE targetNorm (nadd (layerNorm (layers k)) (pointName (eps k)))
  variationApprox : ∀ k,
    nameLE (layerJump (layers k)) (nadd gradientIntegral (pointName (eps k)))
def SobolevPresentationGoal : Prop := ∀ d, 2 ≤ d →
  ∀ s : SobolevApproximation d,
    nameLE (nmul (sobolevFactor d (4^d+2)) s.targetNorm) s.gradientIntegral

def sineName (x : RawName) : RawName := fun k =>
  let v := sinTaylor (k+20) (mid (x (k+24)))
  ⟨v-eps (k+2), v+eps (k+2)⟩
def cosineName (x : RawName) : RawName := fun k =>
  let v := cosTaylor (k+20) (mid (x (k+24)))
  ⟨v-eps (k+2), v+eps (k+2)⟩
def ElementaryTrigGoal : Prop := ∀ x, ValidName x →
  (∀ k, |(x k).lo| ≤ 4 ∧ |(x k).hi| ≤ 4) →
    ValidName (sineName x) ∧ ValidName (cosineName x) ∧
    nameEq (nadd (npow (sineName x) 2) (npow (cosineName x) 2)) (pointName 1)

structure CapData (pi : RawName) where
  radius : RawName
  angle : RawName
  valid : ValidName radius ∧ ValidName angle
  radiusPositive : PositiveBound radius
  angleRange : nameLE (pointName 0) angle ∧ nameLE angle pi
  angleBounds : ∀ k, |(angle k).lo| ≤ 4 ∧ |(angle k).hi| ≤ 4
def capArea {pi : RawName} (c : CapData pi) : RawName :=
  nmul (nmul (nscale 2 pi) (npow c.radius 2))
    (nsub (pointName 1) (cosineName c.angle))
def capLength {pi : RawName} (c : CapData pi) : RawName :=
  nmul (nmul (nscale 2 pi) c.radius) (sineName c.angle)

/-- Denominator-free spherical equality; radius positivity restores the
usual formula L²=4*pi*A-A²/R². No general spherical-curve claim is made. -/
def SphericalCapGoal (pi : RawName) : Prop := ∀ c : CapData pi,
  nameEq (nmul (npow c.radius 2) (npow (capLength c) 2))
    (nsub (nmul (nmul (nscale 4 pi) (npow c.radius 2)) (capArea c))
          (npow (capArea c) 2))

/-- These are the actual fixed-constant analytic targets. -/
def CanonicalPlanarGoal : Prop := PlanarPresentationGoal canonicalPiName
def CanonicalWignerGoal : Prop := WignerPresentationGoal canonicalPiName
def CanonicalCapGoal : Prop := SphericalCapGoal canonicalPiName

/- Remaining geometry bridges, all explicit obligations:
1. Prove enclosure laws and coefficient/degree budgets for raw operations.
2. Derive SupportC2Presentation's bridges from the report's polygonal-area
   and finite Fejer estimates; do not assume a Fourier completeness theorem.
3. Prove BoxAlgorithmsGoal by sorting endpoints and testing common cells;
   implement finite interface incidence for GridCoareaGoal.
4. Supply normApprox and variationApprox for each intended W^{1,1} family.
   Axis-aligned grid approximation alone does NOT imply the Euclidean
   variationApprox contract, because its limit may be anisotropic.
5. For cap unions, prove the finite disjointness/boundary-additivity contract
   and sum the cap identities. The report's exact deficit is the sum of the
   nonnegative cross terms; complement area is 4*pi*R²-A.
6. Compile each fixed presentation's PR routines and its finite precision
   calculations; construct the internal derivations, then check compilation.
-/

end IsoperimetricAnalytic
