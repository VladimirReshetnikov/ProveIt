import Init

namespace SmallCertificates

abbrev Point := Int × Int

def sub (a b : Point) : Point := (a.1 - b.1, a.2 - b.2)

-- In the triangular basis (1,0), (1/2,√3/2).
def sqNorm (p : Point) : Int := p.1*p.1 + p.1*p.2 + p.2*p.2

def sqDist (a b : Point) : Int := sqNorm (sub a b)

-- All coordinates multiplied by 3; all squared lengths multiplied by 9.
theorem tetraHoleCorners :
    [(0,0), (6,0), (0,6), (6,6)].map (sqDist (2,2)) = [12,12,12,48] := by
  decide

inductive Axis where | a | b | c
open Axis

def source : Axis → Point
  | a => (0,0)
  | b => (1,0)
  | c => (0,1)

def flipAcross (p edge1 edge2 : Point) : Point :=
  (edge1.1 + edge2.1 - p.1, edge1.2 + edge2.2 - p.2)

def flipA := flipAcross (source a) (source b) (source c)
def flipB := flipAcross (source b) flipA (source c)
def flipC := flipAcross (source c) flipA flipB

def target : Axis → Point
  | a => flipA
  | b => flipB
  | c => flipC

theorem octFinalVertices :
    (flipA, flipB, flipC) = ((1,1), (0,2), (1,2)) := by
  decide

def axes : List Axis := [a,b,c]

def cornerSq (i j : Axis) : Int := sqDist (source i) (target j)

theorem octCornerTable :
    axes.map (fun i => axes.map (cornerSq i)) =
       [[3,4,7], [1,3,4], [1,1,3]] := by
  decide

def relabel (x y z : Axis) : Axis → Axis
  | a => x
  | b => y
  | c => z

def orders : List (Axis → Axis) :=
  [relabel a b c, relabel a c b, relabel b a c, relabel b c a,
   relabel c a b, relabel c b a]

theorem octStripSum (i j : Axis) :
    (orders.map (fun s => cornerSq (s i) (s j))).foldl (· + ·) 0 = 18 := by
  cases i <;> cases j <;> decide

end SmallCertificates
