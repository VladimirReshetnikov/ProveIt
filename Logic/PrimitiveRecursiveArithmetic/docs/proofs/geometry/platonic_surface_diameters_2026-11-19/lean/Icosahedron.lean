import Std

/-!
Exact integer arithmetic for the two six-face strips and the radial calibration
on the unit icosahedron. All points below are stored with common denominator
six. Proofs by reduction use Lean's kernel.
-/

namespace Platonic.Icosahedron

abbrev Point := Int × Int

def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)
def normSq (p : Point) : Int := p.1*p.1 + p.1*p.2 + p.2*p.2

def source : List Point := [(0, 0), (3, 0), (2, 2)]
def targetOne : List Point := [(6, -18), (3, -15), (4, -14)]
def targetTwo : List Point := [(6, 12), (3, 15), (4, 16)]

/-- Entries are 72 times the mean squared path length. -/
def cornerMatrix : List (List Int) :=
  source.map fun p => (targetOne.zip targetTwo).map fun (q, r) =>
    normSq (sub p q) + normSq (sub p r)

theorem corner_matrix :
    cornerMatrix = [[504, 468, 492], [468, 450, 456], [492, 456, 456]] := by
  decide

/-- A face image written as the three corners in units of one sixth. -/
abbrev Triangle := Point × Point × Point

def fullCharts : List Triangle :=
  [((0, 0), (6, 0), (0, 6)), ((6, 0), (0, 6), (6, 6))]
def halfCharts : List Triangle :=
  [((6, 0), (6, 6), (9, 3)), ((12, 6), (6, 6), (9, 3))]

def sideSquares (t : Triangle) : List Int :=
  let (a, b, m) := t
  [normSq (sub b m), normSq (sub a m), normSq (sub a b)]

theorem isometric_charts :
    fullCharts.map sideSquares = [[36, 36, 36], [36, 36, 36]] ∧
    halfCharts.map sideSquares = [[9, 27, 36], [9, 27, 36]] := by
  decide

/-- The five gluing edge types in order NA, AA, AB, BB, BS. -/
def edgeMidpoints : List Point := [(3, 0), (3, 3), (6, 3), (9, 3), (9, 6)]

theorem calibration_values :
    ([(0, 0), (6, 0), (6, 6), (12, 6)] : List Point).map normSq =
      [0, 36, 108, 252] ∧
    edgeMidpoints.map normSq = [9, 27, 63, 117, 171] := by
  decide

end Platonic.Icosahedron
