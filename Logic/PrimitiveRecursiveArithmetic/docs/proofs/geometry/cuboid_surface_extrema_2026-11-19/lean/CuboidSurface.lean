import Mathlib

/-!
# Intrinsic extremal distances on a rectangular cuboid: formalization outline

STATUS: this is an uncompiled Lean 4 outline, not a completed formal proof.
The intended pin is mathlib 6c9a0a07bbbce9b0205b16c83a17b8458f4bcdf9,
with leanprover/lean4:v4.36.0. See README.md for verified source APIs.

Every unfinished milestone is explicitly marked `sorry`. There are no `axiom`
declarations. The `ring` lemmas are proposed complete algebraic proofs but have
not been compiled in this environment. Definitions use the Euclidean L² norm,
continuous surface curves, and their actual metric variation; they do not
replace the requested intrinsic metric by the ambient chord distance.
-/

noncomputable section

open Set

namespace CuboidSurface

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)

def point2 (x y : ℝ) : E2 := !₂[x, y]
def point3 (x y z : ℝ) : E3 := !₂[x, y, z]

/-- Side lengths after permuting the three coordinate axes. -/
structure Sides where
  a : ℝ
  b : ℝ
  c : ℝ
  a_pos : 0 < a
  ab : a ≤ b
  bc : b ≤ c

namespace Sides

theorem b_pos (s : Sides) : 0 < s.b := lt_of_lt_of_le s.a_pos s.ab
theorem c_pos (s : Sides) : 0 < s.c := lt_of_lt_of_le s.b_pos s.bc

def lengths (s : Sides) : E3 := point3 s.a s.b s.c

end Sides

/-- The solid box is used only to define its boundary and faces. -/
def Solid (s : Sides) : Set E3 :=
  {p | ∀ i : Fin 3, 0 ≤ p i ∧ p i ≤ s.lengths i}

/-- All six closed rectangular faces, including their edges and vertices. -/
def Surface (s : Sides) : Set E3 :=
  {p | p ∈ Solid s ∧ ∃ i : Fin 3, p i = 0 ∨ p i = s.lengths i}

inductive FaceSide where
  | lower
  | upper
  deriving DecidableEq, Fintype

structure Face where
  axis : Fin 3
  side : FaceSide
  deriving DecidableEq, Fintype

def faceCoordinate (s : Sides) (f : Face) : ℝ :=
  match f.side with
  | .lower => 0
  | .upper => s.lengths f.axis

def faceSet (s : Sides) (f : Face) : Set E3 :=
  {p | p ∈ Solid s ∧ p f.axis = faceCoordinate s f}

/-- Distinct-axis faces are adjacent; the two faces of one axis are opposite. -/
def AdjacentFaces (f g : Face) : Prop := f.axis ≠ g.axis

abbrev FaceWord := List Face

def ReducedFaceWord (w : FaceWord) : Prop :=
  w ≠ [] ∧ w.Nodup ∧ w.Chain' AdjacentFaces

def origin : E3 := point3 0 0 0
def oppositeVertex (s : Sides) : E3 := s.lengths
def antipode (s : Sides) (p : E3) : E3 := s.lengths - p

def bottomPoint (x y : ℝ) : E3 := point3 x y 0
def topPoint (s : Sides) (x y : ℝ) : E3 := point3 x y s.c

def topRectangle (s : Sides) : Set E2 :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ s.a ∧ 0 ≤ p 1 ∧ p 1 ≤ s.b}

def quarterRectangle (s : Sides) : Set E2 :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ s.a / 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ s.b / 2}

/-! ## Intrinsic metric from continuous surface paths -/

def unitInterval : Set ℝ := Icc 0 1

/-- A continuous path is defined on ℝ, but only its values on [0,1] matter. -/
structure SurfaceCurve (s : Sides) (p q : E3) where
  toFun : ℝ → E3
  continuousOn : ContinuousOn toFun unitInterval
  source : toFun 0 = p
  target : toFun 1 = q
  onSurface : ∀ t ∈ unitInterval, toFun t ∈ Surface s

/-- Extended length: supremum of all finite sums of successive chord lengths. -/
def curveLength (γ : ℝ → E3) : ℝ≥0∞ := eVariationOn γ unitInterval

/-- This infimum includes every continuous surface path, including infinite-length ones. -/
def intrinsicEDist (s : Sides) (p q : E3) : ℝ≥0∞ :=
  sInf (Set.range fun γ : SurfaceCurve s p q => curveLength γ.toFun)

/-- Finite on Surface s by `intrinsicEDist_ne_top`, which must be proved first. -/
def intrinsicDist (s : Sides) (p q : E3) : ℝ :=
  (intrinsicEDist s p q).toReal

/-- A finite polygon whose every segment lies in one convex closed box face.
The n = 0 case is the constant path. A separate reduction proves n ≤ 6. -/
structure FacePolygon (s : Sides) (p q : E3) where
  n : ℕ
  vertices : Fin (n+1) → E3
  faces : Fin n → Face
  source : vertices 0 = p
  target : vertices (Fin.last n) = q
  start_on_surface : p ∈ Surface s
  segment_source : ∀ i : Fin n, vertices i.castSucc ∈ faceSet s (faces i)
  segment_target : ∀ i : Fin n, vertices i.succ ∈ faceSet s (faces i)

def polygonLength {s : Sides} {p q : E3} (P : FacePolygon s p q) : ℝ :=
  ∑ i : Fin P.n, dist (P.vertices i.castSucc) (P.vertices i.succ)

/-- Alternative to constant-speed compactness: the finite last-visit argument
from the report. This is a proof obligation, not an altered metric definition. -/
theorem curve_has_shorter_face_polygon (s : Sides) {p q : E3}
    (γ : SurfaceCurve s p q) :
    ∃ P : FacePolygon s p q, P.n ≤ 6 ∧
      ENNReal.ofReal (polygonLength P) ≤ curveLength γ.toFun := by
  sorry

/-- This elementary bound follows directly from the complete-lattice infimum. -/
theorem intrinsicEDist_le_length (s : Sides) (p q : E3)
    (γ : SurfaceCurve s p q) :
    intrinsicEDist s p q ≤ curveLength γ.toFun := by
  exact sInf_le ⟨γ, rfl⟩

/-- M1a: connect both endpoints to box vertices by face segments and edge paths. -/
theorem intrinsicEDist_ne_top (s : Sides) {p q : E3}
    (hp : p ∈ Surface s) (hq : q ∈ Surface s) :
    intrinsicEDist s p q ≠ ⊤ := by
  sorry

/-- M1b: compactness plus constant-speed parameterization and lower semicontinuity. -/
theorem shortest_curve_exists (s : Sides) {p q : E3}
    (hp : p ∈ Surface s) (hq : q ∈ Surface s) :
    ∃ γ : SurfaceCurve s p q, curveLength γ.toFun = intrinsicEDist s p q := by
  sorry

/-- M1c: a shortest subarc with both ends in a face equals its straight chord. -/
theorem shortest_curve_face_interval (s : Sides) {p q : E3}
    (γ : SurfaceCurve s p q)
    (hγ : curveLength γ.toFun = intrinsicEDist s p q)
    (f : Face) {u v : ℝ} (hu : u ∈ unitInterval) (hv : v ∈ unitInterval)
    (huv : u ≤ v) (huf : γ.toFun u ∈ faceSet s f)
    (hvf : γ.toFun v ∈ faceSet s f) :
    ∀ t ∈ Icc u v, γ.toFun t ∈ faceSet s f := by
  sorry

/-- M1d: central reflection preserves all admissible lengths and their infimum. -/
theorem antipode_distance (s : Sides) {p q : E3}
    (hp : p ∈ Surface s) (hq : q ∈ Surface s) :
    intrinsicDist s (antipode s p) (antipode s q) = intrinsicDist s p q := by
  sorry

def IsFarthestFrom (s : Sides) (p q : E3) : Prop :=
  p ∈ Surface s ∧ q ∈ Surface s ∧
    ∀ r ∈ Surface s, intrinsicDist s p r ≤ intrinsicDist s p q

def IsDiametralPair (s : Sides) (p q : E3) : Prop :=
  p ∈ Surface s ∧ q ∈ Surface s ∧
    ∀ u ∈ Surface s, ∀ v ∈ Surface s,
      intrinsicDist s u v ≤ intrinsicDist s p q

/-! ## Four principal source images for a fixed vertex -/

def vA (s : Sides) (x y : ℝ) : ℝ := (x + s.c)^2 + y^2
def vB (s : Sides) (x y : ℝ) : ℝ := x^2 + (y + s.c)^2
def vC (s : Sides) (x y : ℝ) : ℝ := (s.a + s.c - x)^2 + (s.a + y)^2
def vD (s : Sides) (x y : ℝ) : ℝ := (s.b + x)^2 + (s.b + s.c - y)^2

def min4 (p q r t : ℝ) : ℝ := min (min p q) (min r t)
def min5 (p q r t u : ℝ) : ℝ := min (min4 p q r t) u

def vertexFaceSq (s : Sides) (x y : ℝ) : ℝ :=
  min4 (vA s x y) (vB s x y) (vC s x y) (vD s x y)

inductive VertexImage where
  | A | B | C | D | E | F | P | Q | R | S
  deriving DecidableEq, Fintype

/-- The exhaustive ten-image table in the report, before domination. -/
def vertexImage (s : Sides) : VertexImage → E2
  | .A => point2 (-s.c) 0
  | .B => point2 0 (-s.c)
  | .C => point2 (s.a + s.c) (-s.a)
  | .D => point2 (-s.b) (s.b + s.c)
  | .E => point2 (2*s.a + s.c) 0
  | .F => point2 0 (2*s.b + s.c)
  | .P => point2 (2*s.a + s.b) (s.b + s.c)
  | .Q => point2 (s.a + s.c) (s.a + 2*s.b)
  | .R => point2 (s.a + s.b) (s.a + s.b + s.c)
  | .S => point2 (s.a + s.b + s.c) (s.a + s.b)

/-- Exact conditions for the two potentially invalid principal unfoldings. -/
def CValid (s : Sides) (x y : ℝ) : Prop := s.a*x + s.c*y ≥ s.a^2
def DValid (s : Sides) (x y : ℝ) : Prop := s.c*x + s.b*y ≥ s.b^2

/-- Proposed complete algebraic lemma; uncompiled in this environment. -/
theorem vA_sub_vB (s : Sides) (x y : ℝ) :
    vA s x y - vB s x y = 2*s.c*(x-y) := by
  unfold vA vB
  ring

/-- Proposed complete algebraic lemma; uncompiled in this environment. -/
theorem vD_sub_vC (s : Sides) (x y : ℝ) :
    vD s x y - vC s x y = 2*(s.a+s.b+s.c)*(x-y+s.b-s.a) := by
  unfold vD vC
  ring

/-- M2a: an invalid C segment is strictly beaten by the valid B segment. -/
theorem invalid_C_dominated (s : Sides) {x y : ℝ}
    (hp : point2 x y ∈ topRectangle s) (hinvalid : ¬ CValid s x y) :
    vB s x y < vC s x y := by
  sorry

/-- M2b: an invalid D segment is strictly beaten by the valid A segment. -/
theorem invalid_D_dominated (s : Sides) {x y : ℝ}
    (hp : point2 x y ∈ topRectangle s) (hinvalid : ¬ DValid s x y) :
    vA s x y < vD s x y := by
  sorry

/-- M2: ten reduced face words, six domination identities, and validity checks. -/
theorem vertex_top_distance_sq (s : Sides) {x y : ℝ}
    (hp : point2 x y ∈ topRectangle s) :
    intrinsicDist s origin (topPoint s x y)^2 = vertexFaceSq s x y := by
  sorry

def baseSq (s : Sides) : ℝ := (s.a+s.b)^2 + s.c^2
def vertexTest (s : Sides) : ℝ := 2*s.c^2 - 2*s.b*s.c - s.a*s.c - s.a*s.b
def vertexDelta (s : Sides) : ℝ := s.a*(s.c-s.b)/(2*s.c)
def vertexW (s : Sides) : E3 :=
  point3 (s.a-vertexDelta s) (s.b-vertexDelta s) s.c

def vertexWSq (s : Sides) : ℝ :=
  (s.b^2+s.c^2)*(s.a^2+2*s.a*s.c+2*s.c^2)/(2*s.c^2)

def vertexMaxSq (s : Sides) : ℝ := max (baseSq s) (vertexWSq s)
def vertexRadius (s : Sides) : ℝ := Real.sqrt (vertexMaxSq s)

def vertexWitness (s : Sides) : E3 :=
  if vertexTest s ≤ 0 then oppositeVertex s else vertexW s

/-- Cross-multiplied gap identity; no division or positivity side conditions. -/
theorem vertex_gap_polynomial (a b c : ℝ) :
    (b^2+c^2)*(a^2+2*a*c+2*c^2) - 2*c^2*((a+b)^2+c^2) =
      a*(c-b)*(2*c^2-2*b*c-a*c-a*b) := by
  ring

/-- M3a: finite nearest-site Voronoi partition; its only interior vertices are U,W. -/
theorem vertex_top_maximum (s : Sides) {x y : ℝ}
    (hp : point2 x y ∈ topRectangle s) :
    vertexFaceSq s x y ≤ vertexMaxSq s := by
  sorry

/-- M3b: explicit two-face paths bound all other faces by the opposite vertex. -/
theorem vertex_other_faces_bound (s : Sides) {p : E3}
    (hp : p ∈ Surface s) (hnot_top : p 2 ≠ s.c) :
    intrinsicDist s origin p^2 ≤ baseSq s := by
  sorry

/-- FIRST MAIN THEOREM: exact maximum from a selected vertex and its coordinates. -/
theorem fixed_vertex_maximum (s : Sides) :
    IsFarthestFrom s origin (vertexWitness s) ∧
      intrinsicDist s origin (vertexWitness s) = vertexRadius s := by
  sorry

/-- Optional full equality classification, including the transition with two points. -/
theorem fixed_vertex_all_maximizers (s : Sides) (q : E3) :
    IsFarthestFrom s origin q ↔
      ((vertexTest s ≤ 0 ∧ q = oppositeVertex s) ∨
       (0 ≤ vertexTest s ∧ q = vertexW s)) := by
  sorry

/-! ## Five antipodal unfolding lengths -/

def a1 (s : Sides) (x y : ℝ) : ℝ := (s.a+s.c)^2 + (s.b-2*y)^2
def a2 (s : Sides) (x y : ℝ) : ℝ := (s.b+s.c)^2 + (s.a-2*x)^2
def a3 (s : Sides) (x y : ℝ) : ℝ :=
  (s.c+x+y)^2 + (s.a+s.b-x-y)^2

def a4 (s : Sides) (x y : ℝ) : ℝ := (s.a+s.b)^2 + (s.c+2*y)^2
def a5 (s : Sides) (x y : ℝ) : ℝ := (s.a+s.b)^2 + (s.c+2*x)^2

def antipodalSq (s : Sides) (x y : ℝ) : ℝ :=
  min5 (a1 s x y) (a2 s x y) (a3 s x y) (a4 s x y) (a5 s x y)

/-- M4: antipodal unfoldings plus dominance and admissibility on a quarter-face. -/
theorem antipodal_bottom_distance_sq (s : Sides) {x y : ℝ}
    (hp : point2 x y ∈ quarterRectangle s) :
    intrinsicDist s (bottomPoint x y) (antipode s (bottomPoint x y))^2 =
      antipodalSq s x y := by
  sorry

/-- M5a: compactness gives a diametral pair. -/
theorem diametral_pair_exists (s : Sides) :
    ∃ p q : E3, IsDiametralPair s p q := by
  sorry

/-- M5b: sphere/involution reduction, via invariant Jordan curve and Brouwer. -/
theorem antipodal_diametral_pair_exists (s : Sides) :
    ∃ p ∈ Surface s, IsDiametralPair s p (antipode s p) := by
  sorry

/-- M5c: the cuboid-specific stronger statement; use local flat geodesic uniqueness. -/
theorem every_diametral_pair_antipodal (s : Sides) {p q : E3}
    (hpq : IsDiametralPair s p q) : q = antipode s p := by
  sorry

/-- M5d: antipodal pairs on the other face pairs are bounded by baseSq. -/
theorem other_antipodal_faces_bound (s : Sides) {p : E3}
    (hp : p ∈ Surface s) (hz0 : p 2 ≠ 0) (hzc : p 2 ≠ s.c) :
    intrinsicDist s p (antipode s p)^2 ≤ baseSq s := by
  sorry

/-! ## Explicit scalar solution; no unspecified optimization oracle -/

/-- Nonnegative square root, with an explicit zero clipping convention. -/
def clippedSqrt (t : ℝ) : ℝ := Real.sqrt (max 0 t)

/-- The scalar function used to determine the squared diameter T. -/
def rootFunction (s : Sides) (T : ℝ) : ℝ :=
  clippedSqrt (T-(s.a+s.c)^2) +
  clippedSqrt (T-(s.b+s.c)^2) +
  clippedSqrt (2*T-(s.a+s.b+s.c)^2)

/-- An explicit upper endpoint whose rootFunction value is greater than c. -/
def rootUpper (s : Sides) : ℝ := (s.a+s.c)^2 + s.b^2

/-- Explicit Dedekind cut for the unique scalar root in the nonvertex regime. -/
def rootCut (s : Sides) : Set ℝ :=
  {T | baseSq s ≤ T ∧ s.c ≤ rootFunction s T}

def rootSquared (s : Sides) : ℝ := sInf (rootCut s)

def diameterMaxSq (s : Sides) : ℝ :=
  if s.c ≤ rootFunction s (baseSq s) then baseSq s else rootSquared s

def diameterValue (s : Sides) : ℝ := Real.sqrt (diameterMaxSq s)

/-- Coordinates of the interior/midline antipodal maximizing point for a given T. -/
def rootX (s : Sides) (T : ℝ) : ℝ :=
  (s.a-clippedSqrt (T-(s.b+s.c)^2))/2

def rootY (s : Sides) (T : ℝ) : ℝ :=
  (s.b-clippedSqrt (T-(s.a+s.c)^2))/2

def diameterWitnessX (s : Sides) : E3 :=
  if s.c ≤ rootFunction s (baseSq s) then origin
  else bottomPoint (rootX s (rootSquared s)) (rootY s (rootSquared s))

def diameterWitnessY (s : Sides) : E3 := antipode s (diameterWitnessX s)

/-- M6a: standard continuity and strict monotonicity of sqrt on nonnegative inputs. -/
theorem rootFunction_continuous (s : Sides) : Continuous (rootFunction s) := by
  sorry

/-- The third radicand is nonnegative at baseSq and then strictly increases. -/
theorem rootFunction_strictMonoOn (s : Sides) :
    StrictMonoOn (rootFunction s) (Ici (baseSq s)) := by
  sorry

/-- A complete explicit interval and equation for the root; no arbitrary selector. -/
theorem root_existsUnique (s : Sides)
    (hregime : rootFunction s (baseSq s) < s.c) :
    ∃! T : ℝ, T ∈ Ioo (baseSq s) (rootUpper s) ∧ rootFunction s T = s.c := by
  sorry

/-- M6b: identify the infimum definition with that uniquely characterized root. -/
theorem rootSquared_spec (s : Sides)
    (hregime : rootFunction s (baseSq s) < s.c) :
    rootSquared s ∈ Ioo (baseSq s) (rootUpper s) ∧
      rootFunction s (rootSquared s) = s.c := by
  sorry

/-- Supports certified bisection: comparisons with F determine the root interval. -/
theorem rootSquared_comparison (s : Sides)
    (hregime : rootFunction s (baseSq s) < s.c)
    {T : ℝ} (hT : baseSq s ≤ T) :
    (T ≤ rootSquared s ↔ rootFunction s T ≤ s.c) := by
  sorry

/-- M6c: the displayed root coordinates are within the quarter-face. -/
theorem root_witness_in_quarter (s : Sides)
    (hregime : rootFunction s (baseSq s) < s.c) :
    point2 (rootX s (rootSquared s)) (rootY s (rootSquared s)) ∈
      quarterRectangle s := by
  sorry

/-- M6d: algebraic optimum of the five explicitly given squared lengths. -/
theorem antipodal_quarter_maximum (s : Sides) {x y : ℝ}
    (hp : point2 x y ∈ quarterRectangle s) :
    antipodalSq s x y ≤ diameterMaxSq s := by
  sorry

/-- M6e: the displayed coordinate formula attains that bound. -/
theorem root_witness_attains (s : Sides)
    (hregime : rootFunction s (baseSq s) < s.c) :
    antipodalSq s (rootX s (rootSquared s)) (rootY s (rootSquared s)) =
      rootSquared s := by
  sorry

/-- SECOND MAIN THEOREM: exact unrestricted diameter, with both endpoints explicit. -/
theorem free_endpoints_maximum (s : Sides) :
    IsDiametralPair s (diameterWitnessX s) (diameterWitnessY s) ∧
      intrinsicDist s (diameterWitnessX s) (diameterWitnessY s) =
        diameterValue s := by
  sorry

/-- THIRD MAIN THEOREM: exactly when freeing the initial vertex helps. -/
theorem strict_improvement_iff (s : Sides) :
    vertexRadius s < diameterValue s ↔
      rootFunction s (baseSq s) < s.c := by
  sorry

/-- Optional explicit radical branch, avoiding a scalar solve in that regime. -/
def radicalBranchTest (s : Sides) : Prop :=
  s.a^2*s.b^2 ≤ s.c^2*(s.b-s.a)*(s.a+s.b+2*s.c)

def radicalDiameterSq (s : Sides) : ℝ :=
  s.b^2 + 3*s.c^2 + 2*s.b*(s.a+s.c) -
    2*s.c*Real.sqrt ((s.b+s.c)^2 - 2*s.a*(s.c-s.b) - s.a^2)

/-- M7: substitute and check signs before squaring; do not rely on numeric roots. -/
theorem radical_branch_formula (s : Sides)
    (hregime : rootFunction s (baseSq s) < s.c)
    (hbranch : radicalBranchTest s) :
    diameterMaxSq s = radicalDiameterSq s := by
  sorry

end CuboidSurface
