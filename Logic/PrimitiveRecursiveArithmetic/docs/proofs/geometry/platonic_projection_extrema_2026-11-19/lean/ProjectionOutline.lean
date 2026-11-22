import Mathlib

/-!
# Platonic projection extrema: executable definitions and proof interfaces

STATUS: uncompiled outline. No Lean executable was available in the task runtime.
This file contains no `axiom` and no `sorry`. A structure containing proof fields
states obligations; constructing that structure remains necessary. In particular,
the finite checker alone is not an object-theory derivation in iPRA.

The generators below use F(x) = sum_i |g_i dot x|. For a solid of unit edge,
the orthographic projection area is factor * F(x) / sqrt(normSq x).
All exact calculations take place in Q(phi), encoded by pairs of rationals.
-/

namespace PlatonicProjection

structure Golden where
  a : ℚ
  b : ℚ
  deriving DecidableEq, Repr

namespace Golden

def zero : Golden := ⟨0, 0⟩
def one : Golden := ⟨1, 0⟩
def ofRat (q : ℚ) : Golden := ⟨q, 0⟩
def phi : Golden := ⟨0, 1⟩
def invPhi : Golden := ⟨-1, 1⟩
def add (x y : Golden) : Golden := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : Golden) : Golden := ⟨-x.a, -x.b⟩
def sub (x y : Golden) : Golden := add x (neg y)
def mul (x y : Golden) : Golden :=
  ⟨x.a*y.a + x.b*y.b, x.a*y.b + x.b*y.a + x.b*y.b⟩
def sq (x : Golden) : Golden := mul x x
def norm (x : Golden) : ℚ := x.a*x.a + x.a*x.b - x.b*x.b
def inv (x : Golden) : Golden :=
  ⟨(x.a+x.b)/norm x, -x.b/norm x⟩
def div (x y : Golden) : Golden := mul x (inv y)

/-- Exact nonnegative test for a+b phi; all comparisons are rational. -/
def nonneg (x : Golden) : Bool :=
  let A := 2*x.a + x.b
  let B := x.b
  if B = 0 then decide (0 ≤ A)
  else if 0 < B then
    if 0 ≤ A then true else decide (A*A ≤ 5*B*B)
  else
    if 0 ≤ A then decide (5*B*B ≤ A*A) else false

def le (x y : Golden) : Bool := nonneg (sub y x)
def eq (x y : Golden) : Bool := decide (x = y)
def abs (x : Golden) : Golden := if nonneg x then x else neg x
def sum (xs : List Golden) : Golden := xs.foldl add zero

/-- Only the semantic bridge uses Real.sqrt; the checker above does not. -/
noncomputable def eval (x : Golden) : ℝ :=
  (x.a : ℝ) + (x.b : ℝ) * ((1 + Real.sqrt 5) / 2)

end Golden

abbrev Vec3 := Fin 3 → Golden

def vec (x y z : Golden) : Vec3 := ![x,y,z]
def vi (x y z : ℚ) : Vec3 := vec (Golden.ofRat x) (Golden.ofRat y) (Golden.ofRat z)
def vzero : Vec3 := vi 0 0 0
def vadd (x y : Vec3) : Vec3 := fun j => Golden.add (x j) (y j)
def vneg (x : Vec3) : Vec3 := fun j => Golden.neg (x j)
def vsub (x y : Vec3) : Vec3 := vadd x (vneg y)
def scale (a : Golden) (x : Vec3) : Vec3 := fun j => Golden.mul a (x j)
def dot (x y : Vec3) : Golden :=
  Golden.add (Golden.add (Golden.mul (x 0) (y 0)) (Golden.mul (x 1) (y 1))) (Golden.mul (x 2) (y 2))
def cross (x y : Vec3) : Vec3 := vec
  (Golden.sub (Golden.mul (x 1) (y 2)) (Golden.mul (x 2) (y 1)))
  (Golden.sub (Golden.mul (x 2) (y 0)) (Golden.mul (x 0) (y 2)))
  (Golden.sub (Golden.mul (x 0) (y 1)) (Golden.mul (x 1) (y 0)))
def normSq (x : Vec3) : Golden := dot x x
def vIsZero (x : Vec3) : Bool :=
  Golden.eq (x 0) Golden.zero && Golden.eq (x 1) Golden.zero && Golden.eq (x 2) Golden.zero
def det (x y z : Vec3) : Golden := dot x (cross y z)
def vsum (xs : List Vec3) : Vec3 := xs.foldl vadd vzero

/-- Oriented polygon area vector, including the closing edge. -/
def faceAreaVector (ps : List Vec3) : Vec3 :=
  match ps with
  | [] => vzero
  | p :: rest =>
    scale (Golden.ofRat (1/2))
      (vsum ((ps.zip (rest ++ [p])).map fun edge => cross edge.1 edge.2))

/-- Exact algebraic projection; its theorem requires normSq view != 0. -/
def orthogonalProjection (view point : Vec3) : Vec3 :=
  vsub point (scale (Golden.div (dot point view) (normSq view)) view)

/-- Projection along view onto the j-th coordinate plane; requires view j != 0. -/
def obliqueProjection (view point : Vec3) (j : Fin 3) : Vec3 :=
  vsub point (scale (Golden.div (point j) (view j)) view)

structure Data where
  label : String
  generators : List Vec3
  factor : Golden
  lowerFSq : Golden
  upperFSq : Golden

def tetraGenerators : List Vec3 :=
  [vi 1 1 1, vi 1 (-1) (-1), vi (-1) 1 (-1), vi (-1) (-1) 1]

def cubeGenerators : List Vec3 := [vi 1 0 0, vi 0 1 0, vi 0 0 1]

def dodecaGenerators : List Vec3 :=
  let o := Golden.zero
  let u := Golden.one
  let p := Golden.phi
  [vec o u p, vec o u (Golden.neg p), vec u p o,
   vec u (Golden.neg p) o, vec p o u, vec p o (Golden.neg u)]

def icosaGenerators : List Vec3 :=
  let o := Golden.zero
  let r := Golden.invPhi
  let p := Golden.phi
  [vi 1 1 1, vi 1 1 (-1), vi 1 (-1) 1, vi (-1) 1 1,
   vec o r p, vec o r (Golden.neg p), vec r p o,
   vec r (Golden.neg p) o, vec p o r, vec p o (Golden.neg r)]

def tetrahedron : Data :=
  ⟨"tetrahedron", tetraGenerators, Golden.ofRat (1/8), Golden.ofRat 8, Golden.ofRat 16⟩
def cube : Data :=
  ⟨"cube", cubeGenerators, Golden.one, Golden.one, Golden.ofRat 3⟩
def octahedron : Data :=
  ⟨"octahedron", tetraGenerators, Golden.ofRat (1/4), Golden.ofRat 8, Golden.ofRat 16⟩
def dodecahedron : Data :=
  ⟨"dodecahedron", dodecaGenerators, ⟨1/2,1/4⟩, ⟨8,12⟩, ⟨12,16⟩⟩
def icosahedron : Data :=
  ⟨"icosahedron", icosaGenerators, Golden.ofRat (1/4), ⟨20,30⟩, ⟨24,36⟩⟩

def models : List Data := [tetrahedron,cube,octahedron,dodecahedron,icosahedron]

def brightnessF (d : Data) (x : Vec3) : Golden :=
  Golden.sum (d.generators.map fun g => Golden.abs (dot g x))
def brightness (d : Data) (x : Vec3) : Golden :=
  Golden.mul d.factor (brightnessF d x)
def lowerAreaSq (d : Data) : Golden := Golden.mul (Golden.sq d.factor) d.lowerFSq
def upperAreaSq (d : Data) : Golden := Golden.mul (Golden.sq d.factor) d.upperFSq

def signedVector (d : Data) (mask : ℕ) : Vec3 :=
  vsum (d.generators.mapIdx fun i g => if mask.testBit i then g else vneg g)
def signedVectors (d : Data) : List Vec3 :=
  (List.range (2^d.generators.length)).map (signedVector d)

/-- Every unordered pair occurs once. Its negative need not be repeated. -/
def pairRays (d : Data) : List Vec3 :=
  (List.range d.generators.length).flatMap fun i =>
    (List.range i).map fun j =>
      cross (d.generators.getD i vzero) (d.generators.getD j vzero)

def spanCheck (d : Data) : Bool :=
  !(Golden.eq (det (d.generators.getD 0 vzero)
                   (d.generators.getD 1 vzero)
                   (d.generators.getD 2 vzero)) Golden.zero)
def upperCheck (d : Data) : Bool :=
  (signedVectors d).all fun s => Golden.le (normSq s) d.upperFSq
def lowerCheck (d : Data) : Bool :=
  (pairRays d).all fun r =>
    vIsZero r || Golden.le (Golden.mul d.lowerFSq (normSq r)) (Golden.sq (brightnessF d r))

def attainsF (d : Data) (sq : Golden) (x : Vec3) : Bool :=
  !(vIsZero x) && Golden.eq (Golden.sq (brightnessF d x)) (Golden.mul sq (normSq x))

def maxDirection (d : Data) : Vec3 :=
  ((signedVectors d).find? fun s => attainsF d d.upperFSq s).getD vzero
def minDirection (d : Data) : Vec3 :=
  ((pairRays d).find? fun r => attainsF d d.lowerFSq r).getD vzero

/-- Complete finite data check, but its generic soundness still needs proof. -/
def certificateCheck (d : Data) : Bool :=
  Golden.nonneg d.factor && !(Golden.eq d.factor Golden.zero) &&
  Golden.nonneg d.lowerFSq && Golden.nonneg d.upperFSq && spanCheck d && upperCheck d && lowerCheck d &&
  attainsF d d.lowerFSq (minDirection d) && attainsF d d.upperFSq (maxDirection d)

/-- This universal statement is the arithmetic target, not just sample checks. -/
def ExactBounds (d : Data) : Prop :=
  ∀ x : Vec3,
    Golden.le (Golden.mul d.lowerFSq (normSq x)) (Golden.sq (brightnessF d x)) = true ∧
    Golden.le (Golden.sq (brightnessF d x)) (Golden.mul d.upperFSq (normSq x)) = true

/-! Finite cones and the two-stage lower-bound argument. -/

def InCone (ws : List Vec3) (x : Vec3) : Prop :=
  ∀ w ∈ ws, Golden.nonneg (dot w x) = true
def sumNormal (ws : List Vec3) : Vec3 := vsum ws
def InSlice (ws : List Vec3) (x : Vec3) : Prop :=
  InCone ws x ∧ dot (sumNormal ws) x = Golden.one

structure Decomposition (ws : List Vec3) (p : Vec3) where
  count : ℕ
  count_le_four : count ≤ 4
  weight : Fin count → Golden
  point : Fin count → Vec3
  weights_nonnegative : ∀ j, Golden.nonneg (weight j) = true
  weights_sum : Golden.sum (List.ofFn weight) = Golden.one
  reconstruct : vsum (List.ofFn fun j => scale (weight j) (point j)) = p
  point_in_slice : ∀ j, InSlice ws (point j)
  terminal : ∀ j, ∃ a b : Fin ws.length,
    vIsZero (cross (ws.get a) (ws.get b)) = false ∧
    dot (ws.get a) (point j) = Golden.zero ∧
    dot (ws.get b) (point j) = Golden.zero

/-!
To construct Decomposition:
* choose a nonzero tangent d to the slice and current active normals;
* compute t+ and t- by bounded scans over signed slopes;
* split into p+t+d and p-t-d, using positive barycentric coefficients;
* each split raises active rank, so depth <= 2 and leaves <= 4.
The proof and all nonzero-denominator guards are in report.tex, in the
finite extremum theorem and arithmetic-encoding sections. Zero active normals
are handled in the active-rank-zero branch, even when the active list is nonempty.
-/

structure AlgebraicProofObligations where
  order_correct : ∀ x, Golden.nonneg x = true ↔ 0 ≤ Golden.eval x
  addition_correct : ∀ x y,
    Golden.eval (Golden.add x y) = Golden.eval x + Golden.eval y
  multiplication_correct : ∀ x y,
    Golden.eval (Golden.mul x y) = Golden.eval x * Golden.eval y
  inverse_correct : ∀ x, x ≠ Golden.zero →
    Golden.mul x (Golden.inv x) = Golden.one
  lagrange : ∀ x y,
    Golden.sub (Golden.mul (normSq x) (normSq y)) (Golden.sq (dot x y)) =
      normSq (cross x y)
  cone_decomposition : ∀ (d : Data) (mask : ℕ) (p : Vec3),
    spanCheck d = true →
    let ws := d.generators.mapIdx fun i g => if mask.testBit i then g else vneg g
    InSlice ws p → Nonempty (Decomposition ws p)
  generic_soundness : ∀ d, certificateCheck d = true → ExactBounds d
  fixed_checks : ∀ d ∈ models, certificateCheck d = true

/-! Semantic geometric definitions, distinct from the numerical iPRA core. -/

abbrev RVec3 := Fin 3 → ℝ
abbrev RVec2 := Fin 2 → ℝ
def dotR (x y : RVec3) : ℝ := x 0*y 0 + x 1*y 1 + x 2*y 2
noncomputable def evalVec (x : Vec3) : RVec3 := fun j => Golden.eval (x j)

structure ScreenFrame where
  normal : RVec3
  e1 : RVec3
  e2 : RVec3
  normal_unit : dotR normal normal = 1
  e1_unit : dotR e1 e1 = 1
  e2_unit : dotR e2 e2 = 1
  e1_e2 : dotR e1 e2 = 0
  e1_normal : dotR e1 normal = 0
  e2_normal : dotR e2 normal = 0

def screenCoordinates (f : ScreenFrame) (x : RVec3) : RVec2 :=
  ![dotR f.e1 x, dotR f.e2 x]

structure PolyhedronModel where
  vertices : List Vec3
  faces : List (List ℕ)
  rawEdgeSq : Golden

noncomputable def shadow (P : PolyhedronModel) (f : ScreenFrame) : Set RVec2 :=
  convexHull ℝ (Set.range fun i : Fin P.vertices.length =>
    screenCoordinates f (evalVec (P.vertices.get i)))

/-- Unit-edge area, obtained by dividing raw-model area by raw edge square. -/
noncomputable def shadowArea (P : PolyhedronModel) (f : ScreenFrame) : ℝ :=
  (MeasureTheory.volume (shadow P f)).toReal / Golden.eval P.rawEdgeSq

noncomputable def realBrightness (d : Data) (x : RVec3) : ℝ :=
  Golden.eval d.factor *
    (d.generators.map fun g => |dotR (evalVec g) x|)Golden.sum

structure GeometryProofObligations (P : PolyhedronModel) (d : Data) where
  /-- Prove from finite face supporting planes, polygon determinants, and fibers. -/
  brightness_formula : ∀ f, shadowArea P f = realBrightness d f.normal
  /-- Extend the algebraic bounds with the explicit Lipschitz modulus in the report. -/
  real_bounds : ∀ x : RVec3,
    Golden.eval (lowerAreaSq d) * dotR x x ≤ (realBrightness d x)^2 ∧
    (realBrightness d x)^2 ≤ Golden.eval (upperAreaSq d) * dotR x x

/-!
Object-theory completion is specified in ObjectTargetOutline.lean. It must encode
these rational-pair programs as PR symbols and construct Prf PRAAx derivations.
Host-level semantic correctness does not discharge that obligation.

For represented real directions the extension is a schema for each fixed PR
approximation program with a supplied/certified fast-Cauchy modulus. There is no
universal PR evaluator of all PR programs and no second-order quantifier inside
iPRA. The statement over every ordinary real direction is a semantic corollary.
-/

end PlatonicProjection
