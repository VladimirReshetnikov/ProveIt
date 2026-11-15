import Mathlib.Data.Rat.Basic
import Mathlib.Data.List.Basic

/-!+# Rational data definitions for the constructive Jordan project

STATUS: implementation scaffold, not a formal proof of the Jordan theorem.
This file has not been compiled in the delivery environment, which did not
contain Lean.  It has no `sorry`, `axiom`, or noncomputable definition.  The
corresponding exact algorithms have an executed Python reference implementation
in `artifacts/jordan_kernel.py`.  `ROADMAP.md` lists the missing proofs.

These semantic definitions are the first layer.  They do not, by themselves,
produce derivations in the first-order theory `ConciseIPRA.PRAAx`.
-/

namespace ConstructiveJordan

structure QPoint where
  x : ℚ
  y : ℚ
  deriving DecidableEq, Repr

def orient (a b p : QPoint) : ℚ :=
  (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)

def onSegment (p a b : QPoint) : Bool :=
  decide (orient a b p = 0 ∧
    (p.x - a.x) * (p.x - b.x) + (p.y - a.y) * (p.y - b.y) ≤ 0)

/-- Signed crossing of a positive horizontal ray; valid when p is off [a,b]. -/
def edgeIndex (a b p : QPoint) : ℤ :=
  if a.y ≤ p.y ∧ p.y < b.y ∧ 0 < orient a b p then 1
  else if b.y ≤ p.y ∧ p.y < a.y ∧ orient a b p < 0 then -1
  else 0

def cyclicEdges (vertices : List QPoint) : List (QPoint × QPoint) :=
  vertices.zip (vertices.tail ++ vertices.take 1)

def rawIndex (vertices : List QPoint) (p : QPoint) : ℤ :=
  (cyclicEdges vertices).foldl (fun z edge => z + edgeIndex edge.1 edge.2 p) 0

/-- Reject the inadmissible case of a query point on an edge. -/
def index? (vertices : List QPoint) (p : QPoint) : Option ℤ :=
  if (cyclicEdges vertices).any (fun e => onSegment p e.1 e.2) then none
  else some (rawIndex vertices p)

/-- The main proof uses this orientation-independent mod-two value. -/
def parity? (vertices : List QPoint) (p : QPoint) : Option Bool :=
  (index? vertices p).map (fun z => decide (z % 2 = 1))

abbrev Cell := ℤ × ℤ

def center (h : ℚ) (c : Cell) : QPoint :=
  ⟨3 * (c.1 : ℚ) * h, ((c.1 : ℚ) + 2 * (c.2 : ℚ)) * h⟩

def neighbors (c : Cell) : List Cell :=
  [(c.1 + 1, c.2), (c.1, c.2 + 1), (c.1 - 1, c.2 + 1),
   (c.1 - 1, c.2), (c.1, c.2 - 1), (c.1 + 1, c.2 - 1)]

/-- One bounded propagation step on a supplied finite patch and link table. -/
def floodStep (cells : List Cell) (green : Cell → Cell → Bool)
    (seen : List Cell) : List Cell :=
  cells.filter fun c => seen.contains c ||
    (neighbors c).any (fun d => seen.contains d && green d c)

/-- V rounds suffice on a graph with V vertices.  This is deliberately bounded. -/
def flood (cells : List Cell) (green : Cell → Cell → Bool)
    (root : Cell) : List Cell :=
  (List.range cells.length).foldl (fun seen _ => floodStep cells green seen) [root]

/-- A finite certificate records parents as array indices, never as a choice. -/
structure RouteCertificate where
  vertices : List QPoint
  clearanceNumerator : ℕ
  clearanceDenominator : ℕ
  parentIndices : List ℕ
  deriving Repr

end ConstructiveJordan
