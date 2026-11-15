import Mathlib
import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Constructive isoperimetry: definitions and internal proof targets

STATUS: UNCOMPILED FORMALIZATION OUTLINE.

This file defines finite data, specifications, and the exact kind of internal
iPRA theorem to be constructed.  It does NOT supply the internal proofs of
the isoperimetric, Brunn--Minkowski, or hypercube theorems.  It contains no
`sorry` declarations and introduces no axioms.  A proposition named `Goal`
is an obligation, not an established theorem.

Repository API inspected at ProveIt commit
22afac4c9db7a0e060c081cc11db0dc96fe59e93; Lean 4.32.0, Mathlib
81a5d257c8e410db227a6665ed08f64fea08e997.

`Mathlib` is used only for convenient external finite data.  The internal
layer must encode this data by naturals and compile each fixed checker to
ConciseIPRA.PR.  Proving an external proposition about Nat or Rat does not
construct an inhabitant of `Prf PRAAx [] ...`.
-/

namespace IsoperimetricOutline

open scoped BigOperators

structure QPoint where
  x : ℚ
  y : ℚ
  deriving Repr, DecidableEq

def origin : QPoint := ⟨0, 0⟩
def subPoint (p q : QPoint) : QPoint := ⟨p.x - q.x, p.y - q.y⟩
def normSq (p : QPoint) : ℚ := p.x ^ 2 + p.y ^ 2
def cross (p q : QPoint) : ℚ := p.x * q.y - p.y * q.x
abbrev Polygon := List QPoint

def vertex (p : Polygon) (i : ℕ) : QPoint := p.getD i origin
def nextVertex (p : Polygon) (i : ℕ) : QPoint :=
  vertex p ((i + 1) % p.length)
def edge (p : Polygon) (i : ℕ) : QPoint :=
  subPoint (nextVertex p i) (vertex p i)
def signedArea (p : Polygon) : ℚ :=
  (∑ i ∈ Finset.range p.length, cross (vertex p i) (nextVertex p i)) / 2
def edgeEnergy (p : Polygon) : ℚ :=
  ∑ i ∈ Finset.range p.length, normSq (edge p i)

def UpperLengths (p : Polygon) (u : List ℚ) : Prop :=
  u.length = p.length ∧
  ∀ i < p.length, 0 ≤ u.getD i 0 ∧ normSq (edge p i) ≤ (u.getD i 0) ^ 2

/-- `piLower` must be the particular rational algorithm in the report,
with its enclosure theorem; an arbitrary function is not a substitute. -/
def PolygonGoal (piLower : ℕ → ℚ) : Prop :=
  ∀ (p : Polygon) (u : List ℚ) (k : ℕ), UpperLengths p u →
    4 * piLower k * |signedArea p| ≤ u.sum ^ 2 + 1 / (2 : ℚ) ^ k

/-- Radical-free form of the two triangle inequalities.
For an actual triangle, Heron(a,b,c) = 16 * area^2. -/
def heron (a b c : ℚ) : ℚ :=
  2 * a^2 * b^2 + 2 * b^2 * c^2 + 2 * c^2 * a^2 - a^4 - b^4 - c^4
def TriangleSides (a b c : ℚ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b
def TriangleGoal : Prop :=
  ∀ a b c : ℚ, TriangleSides a b c →
    27 * heron a b c ≤ (a + b + c)^4 ∧
    (heron a b c)^3 ≤ 27 * (a*b*c)^4

structure SupportMode where
  cosine : ℚ
  sine : ℚ
  deriving Repr
def modeSq (c : SupportMode) : ℚ := c.cosine^2 + c.sine^2

/-- Index i stores frequency i+2, so translations (frequency 1) are omitted. -/
def supportDeficit (cs : List SupportMode) : ℚ :=
  ∑ i ∈ Finset.range cs.length,
    (((i + 2 : ℕ) : ℚ)^2 - 1) * modeSq (cs.getD i ⟨0, 0⟩)
def evenSupportDeficit (cs : List SupportMode) : ℚ :=
  ∑ i ∈ Finset.range cs.length,
    if (i + 2) % 2 = 0 then
      (((i + 2 : ℕ) : ℚ)^2 - 1) * modeSq (cs.getD i ⟨0, 0⟩)
    else 0
def oddSupportDeficit (cs : List SupportMode) : ℚ :=
  ∑ i ∈ Finset.range cs.length,
    if (i + 2) % 2 = 1 then
      (((i + 2 : ℕ) : ℚ)^2 - 1) * modeSq (cs.getD i ⟨0, 0⟩)
    else 0
def evenModesZero (cs : List SupportMode) : Prop :=
  ∀ i < cs.length, (i + 2) % 2 = 0 →
    (cs.getD i ⟨0, 0⟩).cosine = 0 ∧ (cs.getD i ⟨0, 0⟩).sine = 0
def WignerFiniteGoal : Prop :=
  ∀ cs : List SupportMode,
    supportDeficit cs = evenSupportDeficit cs + oddSupportDeficit cs ∧
    0 ≤ evenSupportDeficit cs ∧ 0 ≤ oddSupportDeficit cs ∧
    (evenSupportDeficit cs = 0 ↔ evenModesZero cs)

structure QBox (d : ℕ) where
  lo : Fin d → ℚ
  hi : Fin d → ℚ

def boxValid {d : ℕ} (b : QBox d) : Prop := ∀ i, b.lo i < b.hi i
def boxVolume {d : ℕ} (b : QBox d) : ℚ :=
  ∏ i : Fin d, (b.hi i - b.lo i)
def boxesSeparated {d : ℕ} (b c : QBox d) : Prop :=
  ∃ i, b.hi i ≤ c.lo i ∨ c.hi i ≤ b.lo i
abbrev BoxUnion (d : ℕ) := List (QBox d)
def disjointBoxUnion {d : ℕ} (bs : BoxUnion d) : Prop :=
  (∀ b ∈ bs, boxValid b) ∧ bs.Pairwise boxesSeparated
def disjointVolume {d : ℕ} (bs : BoxUnion d) : ℚ :=
  (bs.map boxVolume).sum
def minkowskiBox {d : ℕ} (b c : QBox d) : QBox d :=
  ⟨fun i => b.lo i + c.lo i, fun i => b.hi i + c.hi i⟩

/- `dissect` is to be implemented by sorting the finitely many endpoints on
every coordinate axis and retaining occupied elementary grid cells.  It must
be verified on arbitrary lists, including overlapping boxes.  Merely summing
the volumes of pairwise Minkowski boxes would overcount their overlaps. -/
def FiniteBMGoal
    (dissect : {d : ℕ} → BoxUnion d → BoxUnion d) : Prop :=
  ∀ (d : ℕ) (x y : BoxUnion d) (q : ℚ),
    0 < d → disjointBoxUnion x → disjointBoxUnion y →
    0 < disjointVolume x → 0 < disjointVolume y → 0 ≤ q →
    q^d * disjointVolume x ≤ disjointVolume y →
    disjointVolume x * (1 + q)^d ≤
      disjointVolume (dissect (x.flatMap (fun a => y.map (minkowskiBox a))))

/-- An explicit finite-precision upper bound on outer-volume growth.
`parallelVolume m` is a rational upper approximation at epsilon=2^(-m).
`volume` and `perimeter` are rational names with separate Cauchy certificates.
The report supplies the representation and error conventions.  This record
only exposes the modulus that the formal implementation must carry. -/
structure OuterVolumeData where
  volume : ℕ → ℚ
  perimeter : ℕ → ℚ
  parallelVolume : ℕ → ℕ → ℚ
  outerModulus : ℕ → ℕ
  upperLaw : ∀ k m, outerModulus k ≤ m →
    parallelVolume m k ≤ volume k +
      (perimeter k + 1 / (2 : ℚ)^k) / (2 : ℚ)^m

def memMask (s v : ℕ) : Prop := (s / 2^v) % 2 = 1
instance (s v : ℕ) : Decidable (memMask s v) := inferInstance
def flipBit (v i : ℕ) : ℕ :=
  if (v / 2^i) % 2 = 0 then v + 2^i else v - 2^i
def cubeCard (d s : ℕ) : ℕ :=
  ((Finset.range (2^d)).filter (memMask s)).card
def edgeBoundary (d s : ℕ) : ℕ :=
  ∑ v ∈ Finset.range (2^d),
    if memMask s v then
      ∑ i ∈ Finset.range d, if memMask s (flipBit v i) then 0 else 1
    else 0
def internalEdges (d s : ℕ) : ℕ :=
  ∑ v ∈ Finset.range (2^d),
    if memMask s v then
      ∑ i ∈ Finset.range d,
        if v < flipBit v i ∧ memMask s (flipBit v i) then 1 else 0
    else 0
def closedNeighborhoodMember (d s v : ℕ) : Prop :=
  memMask s v ∨ ∃ i ∈ Finset.range d, memMask s (flipBit v i)
instance (d s v : ℕ) : Decidable (closedNeighborhoodMember d s v) :=
  inferInstance
def closedNeighborhoodCard (d s : ℕ) : ℕ :=
  ((Finset.range (2^d)).filter (closedNeighborhoodMember d s)).card
def hammingWeight (d v : ℕ) : ℕ :=
  ∑ i ∈ Finset.range d, if (v / 2^i) % 2 = 1 then 1 else 0
def lexBefore (d u v : ℕ) : Prop :=
  ∃ i ∈ Finset.range d,
    (u / 2^i) % 2 = 1 ∧ (v / 2^i) % 2 = 0 ∧
    ∀ j ∈ Finset.range i, (u / 2^j) % 2 = (v / 2^j) % 2
instance (d u v : ℕ) : Decidable (lexBefore d u v) := inferInstance
def simplicialBefore (d u v : ℕ) : Prop :=
  hammingWeight d u < hammingWeight d v ∨
    (hammingWeight d u = hammingWeight d v ∧ lexBefore d u v)
instance (d u v : ℕ) : Decidable (simplicialBefore d u v) := inferInstance
def simplicialRank (d v : ℕ) : ℕ :=
  ((Finset.range (2^d)).filter (fun u => simplicialBefore d u v)).card
def initialMask (d k : ℕ) : ℕ :=
  ∑ v ∈ Finset.range (2^d), if simplicialRank d v < k then 2^v else 0
def HypercubeEdgeGoal : Prop :=
  ∀ d s : ℕ,
    2^(2 * internalEdges d s) ≤ (cubeCard d s)^(cubeCard d s) ∧
    d * cubeCard d s = 2 * internalEdges d s + edgeBoundary d s
def HarperGoal : Prop :=
  ∀ d s : ℕ,
    closedNeighborhoodCard d (initialMask d (cubeCard d s)) ≤
      closedNeighborhoodCard d s
def HarperThresholdGoal : Prop :=
  ∀ d r s : ℕ, r ≤ d →
    (∑ i ∈ Finset.range (r + 1), Nat.choose d i) ≤ cubeCard d s →
    (∑ i ∈ Finset.range (r + 2), Nat.choose d i) ≤ closedNeighborhoodCard d s

end IsoperimetricOutline

namespace LeanProofs.ConciseIPRA.IsoperimetricOutline

/- This is external Lean semantics for a fixed PR syntax tree.  It is NOT a
claim that there is a primitive recursive universal evaluator for all PR
programs.  Each concrete checker must be compiled separately. -/
def evalPR : {k : ℕ} → PR k → (Fin k → ℕ) → ℕ
  | _, .zero, _ => 0
  | _, .succ, v => Nat.succ (v 0)
  | _, .proj i, v => v i
  | _, .comp f gs, v => evalPR f (fun i => evalPR (gs i) v)
  | _, .prec f g, v =>
      Nat.rec (evalPR f (fun i => v i.succ))
        (fun n a => evalPR g (Fin.cases n (Fin.cases a (fun i => v i.succ))))
        (v 0)

/-- A checker is a unary natural-number function after all finite input data
has been packed.  Zero means the implication being checked is true; malformed
input or false hypotheses must therefore return zero. -/
structure CompiledChecker (spec : ℕ → ℕ) where
  symbol : PR 1
  semantics : ∀ n, evalPR symbol (fun _ => n) = spec n

def checkerFormula (c : PR 1) : Fm PTm 0 :=
  Fm.all (Fm.eq (PTm.app c (fun _ => PTm.var 0)) PTm.zero)

/-- The actual target for each specified checker.  Supplying only a proof
that `spec n = 0` in Lean's ambient logic does not fill this target. -/
def InternalGoal {spec : ℕ → ℕ} (c : CompiledChecker spec) : Prop :=
  Prf PRAAx [] (checkerFormula c.symbol)

/-- This conditional bridge reuses the verified repository translation.
Its hypothesis is the missing internal theorem, not a mere numerical test. -/
theorem transferToNative {spec : ℕ → ℕ} (c : CompiledChecker spec)
    (h : InternalGoal c) :
    NPrf [] (NFm.ofPRA (checkerFormula c.symbol)) :=
  (pra_iff_native).mp h

/- IMPLEMENTATION TARGETS, deliberately not declared as proved theorems:

1. Codec: signed integers and positive-denominator rationals, lists, polygons,
   Fourier coefficient arrays, box lists, and graph masks; prove totality and
   decoding laws internally.  Reject malformed values by returning success
   for the implication under consideration.
2. Compile fixed arithmetic routines into PR syntax: sums/products, sorting,
   bounded searches, rational root and pi enclosures, grid dissection, and
   the finite certificates described in the report.
3. Construct internal lemmas for ordered arithmetic and each finite identity.
   Use PRA.qfInd with an explicit Fm.QF witness; bounded quantifiers first
   become primitive-recursive Boolean folds.  Strong induction becomes a
   prefix table invariant with a known bound.
4. Construct one InternalGoal inhabitant for each theorem-specific checker.
   Record precise theorem assumptions and the code-to-geometry bridge.
5. Instantiate curve/region presentations one fixed PR family at a time.
   Their moduli and validity proofs are inputs.  Do not infer that arbitrary
   Cauchy sequences, smooth sets, or rectifiable curves have such data.
6. Audit every finished theorem with #print axioms, checking both the ambient
   dependencies and the actual internal target.  Run lake build and report
   which files have genuinely elaborated.  No compilation was available here.
-/

end LeanProofs.ConciseIPRA.IsoperimetricOutline
