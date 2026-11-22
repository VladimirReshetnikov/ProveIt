import Mathlib

/-!
# Cuboid surface geodesics: Lean formalization blueprint

This is a theorem-specification and implementation roadmap, not a completed
formalization.  Statements with `sorry` identify the remaining geometric,
topological, and optimization obligations.  `FiniteAlgebra.lean` separates the
identities that should close by `ring`, `field_simp`, and `nlinarith`.

The design deliberately uses an intrinsic length metric: a path must remain on
the boundary, so no Euclidean chord through the interior is admitted.
-/

namespace CuboidSurface

noncomputable section

abbrev Point3 := Fin 3 → ℝ
abbrev SideLengths := Fin 3 → ℝ

/-- Closed axis-aligned cuboid `[0,s 0] x [0,s 1] x [0,s 2]`. -/
def InCuboid (s : SideLengths) (p : Point3) : Prop :=
  ∀ i, 0 ≤ p i ∧ p i ≤ s i

/-- Boundary membership: at least one coordinate is on an extreme face. -/
def OnSurface (s : SideLengths) (p : Point3) : Prop :=
  InCuboid s p ∧ ∃ i, p i = 0 ∨ p i = s i

/-- Euclidean norm in ambient `R^3`. -/
def norm3 (p : Point3) : ℝ := Real.sqrt (∑ i, (p i) ^ 2)

def dist3 (p q : Point3) : ℝ := norm3 (p - q)

/-- A finite partition of `[0,1]`.  A production implementation can use a
strictly monotone `Fin (n+1) -> Icc 0 1`; the list presentation is convenient
for refinement lemmas. -/
structure Partition where
  points : List ℝ
  nonempty : points ≠ []
  head_zero : points.head? = some 0
  last_one : points.getLast? = some 1
  chain_strict : points.Pairwise (· < ·)

/-- Sum of chord lengths along a partition.  The executable definition should
fold over adjacent pairs in `P.points`. -/
def partitionVariation (γ : ℝ → Point3) (P : Partition) : ℝ :=
  ((P.points.zip P.points.tail).map (fun uv => dist3 (γ uv.1) (γ uv.2))).sum

/-- Rectifiable-curve length as the supremum of all finite variations. -/
def curveLength (γ : ℝ → Point3) : ℝ :=
  sSup {r : ℝ | ∃ P : Partition, r = partitionVariation γ P}

structure SurfacePath (s : SideLengths) (p q : Point3) where
  toFun : ℝ → Point3
  continuousOn : ContinuousOn toFun (Set.Icc 0 1)
  start_eq : toFun 0 = p
  end_eq : toFun 1 = q
  stays_on_surface : ∀ t ∈ Set.Icc (0 : ℝ) 1, OnSurface s (toFun t)

/-- Intrinsic length distance on the cuboid boundary. -/
def intrinsicDist (s : SideLengths) (p q : Point3) : ℝ :=
  sInf {r : ℝ | ∃ γ : SurfacePath s p q, r = curveLength γ.toFun}

/-- Six named faces, used for the finite face-chain classification. -/
inductive Face
  | x0 | x1 | y0 | y1 | z0 | z1
  deriving DecidableEq, Fintype

namespace Face

def axis : Face → Fin 3
  | x0 | x1 => 0
  | y0 | y1 => 1
  | z0 | z1 => 2

def boundaryValue (s : SideLengths) : Face → ℝ
  | x0 | y0 | z0 => 0
  | x1 => s 0
  | y1 => s 1
  | z1 => s 2

end Face

/-- Membership in one named closed face. -/
def OnFace (s : SideLengths) (f : Face) (p : Point3) : Prop :=
  InCuboid s p ∧ p (Face.axis f) = Face.boundaryValue s f

/-- Two cuboid faces share an edge exactly when they fix different axes. -/
def FaceAdjacent (f g : Face) : Prop := Face.axis f ≠ Face.axis g

/-- `f,g` occur consecutively in `chain`. -/
def Consecutive (chain : List Face) (f g : Face) : Prop :=
  ∃ before after, chain = before ++ f :: g :: after

/-- A reduced chain has no repeated face and consecutive faces share an edge. -/
def ReducedFaceChain (chain : List Face) : Prop :=
  chain ≠ [] ∧ chain.Nodup ∧ chain.Chain' FaceAdjacent

abbrev Point2 := Fin 2 → ℝ

def norm2 (p : Point2) : ℝ := Real.sqrt (∑ i, (p i) ^ 2)
def dist2 (p q : Point2) : ℝ := norm2 (p - q)

/-- A precise certificate that a reduced face chain has been unfolded into one
plane.  `chart f` is an isometry on every used face; charts agree on common
edges; and the straight segment between the endpoint images is covered by the
unfolded faces.  The final field records that this segment realizes the
intrinsic infimum. -/
structure UnfoldingWitness
    (s : SideLengths) (p q : Point3) where
  chain : List Face
  reduced : ReducedFaceChain chain
  first last : Face
  head_eq : chain.head? = some first
  last_eq : chain.getLast? = some last
  p_on_first : OnFace s first p
  q_on_last : OnFace s last q
  chart : Face → Point3 → Point2
  face_isometry :
    ∀ f ∈ chain, ∀ u v,
      OnFace s f u → OnFace s f v →
        dist2 (chart f u) (chart f v) = dist3 u v
  edge_glue :
    ∀ f g, Consecutive chain f g → ∀ r,
      OnFace s f r → OnFace s g r → chart f r = chart g r
  pImage qImage : Point2
  pImage_eq : pImage = chart first p
  qImage_eq : qImage = chart last q
  segment_covered :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ f ∈ chain, ∃ r,
      OnFace s f r ∧
      chart f r = (1 - t) • pImage + t • qImage
  realizes_distance : intrinsicDist s p q = dist2 pImage qImage

/-- Every pair of surface points admits a shortest polygonal path whose face
chain unfolds to a straight Euclidean segment.  This is the principal general
polyhedral-geometry theorem needed before the finite cuboid enumeration. -/
theorem shortest_path_unfolds
    (s : SideLengths) (hs : ∀ i, 0 < s i)
    (p q : Point3) (hp : OnSurface s p) (hq : OnSurface s q) :
    Nonempty (UnfoldingWitness s p q) := by
  sorry

section SortedBox

variable {A B C : ℝ}
variable (hA : 0 < A) (hAB : A ≤ B) (hBC : B ≤ C)

/-- Baseline distance between opposite vertices. -/
def L0 (A B C : ℝ) : ℝ := Real.sqrt ((A + B) ^ 2 + C ^ 2)

/-- Fixed-vertex decision expression. -/
def fixedK (A B C : ℝ) : ℝ := 2 * C ^ 2 - 2 * B * C - A * C - A * B

def fixedDelta (A B C : ℝ) : ℝ := A * (C - B) / (2 * C)

def fixedRadius (A B C : ℝ) : ℝ :=
  Real.sqrt ((B ^ 2 + C ^ 2) * (A ^ 2 + 2 * A * C + 2 * C ^ 2) /
    (2 * C ^ 2))

/-- Exact four-source formula for a point `(p,q,C)` on the top face. -/
theorem top_face_source_formula
    (p q : ℝ) (hp : 0 ≤ p ∧ p ≤ A) (hq : 0 ≤ q ∧ q ≤ B) :
    intrinsicDist ![A, B, C] ![0, 0, 0] ![p, q, C] ^ 2 =
      min ((p + C) ^ 2 + q ^ 2)
        (min ((p - A - C) ^ 2 + (q + A) ^ 2)
          (min (p ^ 2 + (q + C) ^ 2)
            ((p + B) ^ 2 + (q - B - C) ^ 2))) := by
  sorry

/-- Fixed-vertex theorem in sorted coordinates. -/
theorem fixed_vertex_farthest :
    let X : Point3 := ![0, 0, 0]
    if fixedK A B C ≤ 0 then
      (∀ Y, OnSurface ![A, B, C] Y →
        intrinsicDist ![A, B, C] X Y ≤ L0 A B C) ∧
      intrinsicDist ![A, B, C] X ![A, B, C] = L0 A B C
    else
      let δ := fixedDelta A B C
      let Y : Point3 := ![A - δ, B - δ, C]
      (∀ Z, OnSurface ![A, B, C] Z →
        intrinsicDist ![A, B, C] X Z ≤ fixedRadius A B C) ∧
      intrinsicDist ![A, B, C] X Y = fixedRadius A B C := by
  sorry

/-- Five squared unfolding lengths for an antipodal pair. -/
def d1Sq (A B C x y : ℝ) := (A + C) ^ 2 + (B - 2 * y) ^ 2
def d2Sq (A B C x y : ℝ) := (B + C) ^ 2 + (A - 2 * x) ^ 2
def d3Sq (A B C x y : ℝ) := (C + x + y) ^ 2 + (A + B - x - y) ^ 2
def d4Sq (A B C x y : ℝ) := (A + B) ^ 2 + (C + 2 * y) ^ 2
def d5Sq (A B C x y : ℝ) := (A + B) ^ 2 + (C + 2 * x) ^ 2

/-- Exact distance formula after central-symmetry normalization. -/
theorem antipodal_five_unfoldings
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ A / 2) (hy : 0 ≤ y ∧ y ≤ B / 2) :
    intrinsicDist ![A, B, C] ![x, y, 0] ![A - x, B - y, C] ^ 2 =
      min (d1Sq A B C x y)
        (min (d2Sq A B C x y)
          (min (d3Sq A B C x y)
            (min (d4Sq A B C x y) (d5Sq A B C x y)))) := by
  sorry

/-- The strong antipodal lemma used to reduce arbitrary endpoint pairs. -/
theorem diametral_pair_is_centrally_symmetric
    (P Q : Point3)
    (hP : OnSurface ![A, B, C] P) (hQ : OnSurface ![A, B, C] Q)
    (hdiam : ∀ U V, OnSurface ![A, B, C] U → OnSurface ![A, B, C] V →
      intrinsicDist ![A, B, C] U V ≤ intrinsicDist ![A, B, C] P Q) :
    Q = ![A - P 0, B - P 1, C - P 2] := by
  sorry

/-- Region in which opposite vertices realize the intrinsic diameter. -/
def InME (A B C : ℝ) : Prop :=
  Real.sqrt (max 0 (A ^ 2 + 2 * A * B - 2 * B * C)) +
    Real.sqrt (max 0 (B ^ 2 + 2 * A * B - 2 * A * C)) ≥
      2 * C - A - B

def diameterSplit (A B C : ℝ) : ℝ :=
  A ^ 2 * B ^ 2 - C ^ 2 * (B - A) * (A + B + 2 * C)

/-- Boundary-case coordinate. -/
def boundaryTau (A B C : ℝ) : ℝ :=
  (B + C - Real.sqrt ((B + C) ^ 2 - 2 * A * (C - B) - A ^ 2)) / 2

def boundaryDiameter (A B C : ℝ) : ℝ :=
  Real.sqrt (B ^ 2 + 3 * C ^ 2 + 2 * B * (A + C) -
    2 * C * Real.sqrt ((B + C) ^ 2 - 2 * A * (C - B) - A ^ 2))

/-- Strictly increasing function whose unique zero gives the interior-case
intrinsic diameter. -/
def rootFunction (A B C ell : ℝ) : ℝ :=
  Real.sqrt (ell ^ 2 - (A + C) ^ 2) +
  Real.sqrt (ell ^ 2 - (B + C) ^ 2) +
  Real.sqrt (2 * ell ^ 2 - (A + B + C) ^ 2) - C

/-- Existence and uniqueness of the scalar root on the theorem's interval. -/
theorem interior_root_unique
    (hout : ¬ InME A B C) (hQ : 0 < diameterSplit A B C) :
    ∃! ell : ℝ,
      max (B + C) (L0 A B C) ≤ ell ∧ rootFunction A B C ell = 0 := by
  sorry

/-- Final intrinsic-diameter theorem.  In a finished development, define
`surfaceDiameter` as a `sSup` over pairs and split on `InME` and
`diameterSplit`; the coordinates in the paper are then witnesses. -/
theorem intrinsic_diameter_complete : True := by
  -- 1. Reduce to antipodal pairs by `diametral_pair_is_centrally_symmetric`.
  -- 2. Apply `antipodal_five_unfoldings`.
  -- 3. Prove the ME criterion and the Q<=0 / Q>0 optimization lemmas.
  -- 4. Supply the explicit endpoint coordinates in all three cases.
  trivial

end SortedBox

end

end CuboidSurface
