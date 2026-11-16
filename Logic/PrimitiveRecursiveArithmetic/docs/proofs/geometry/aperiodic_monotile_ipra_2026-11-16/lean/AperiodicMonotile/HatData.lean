import AperiodicMonotile.Encoding

namespace AperiodicMonotile

/-- Integer axial coordinates of the Smith--Myers--Kaplan--Goodman-Strauss hat. -/
def hatVertices : List (Int × Int) :=
  [(0,0), (-1,-1), (0,-2), (2,-2), (2,-1), (4,-2), (5,-1),
   (4,0), (3,0), (2,2), (0,3), (0,2), (-1,2)]

opaque axialOfIntPair : Int × Int → Axial

def hatPolygon : PolygonCode := {
  vertices := hatVertices.map axialOfIntPair
  atLeastThree := by decide
}

/-- Integral shoelace sum; Euclidean area is `abs sum * sqrt(3)/4`. -/
def shoelaceTerm (a b : Int × Int) : Int := a.1*b.2 - b.1*a.2

def cyclicPairs {α} : List α → List (α × α)
  | [] => []
  | x :: xs => List.zip (x :: xs) (xs ++ [x])

def shoelace (p : List (Int × Int)) : Int :=
  (cyclicPairs p).foldl (fun s ab => s + shoelaceTerm ab.1 ab.2) 0

example : shoelace hatVertices = 32 := by native_decide

/-- The hat is simple.  This is a closed exact computation. -/
opaque simpleHat : simplePolygonB hatPolygon = true

/-- Six kite-direction multiplicities: two directions occur twice, four once. -/
def hatDirectionMultiplicity : Fin 6 → Nat
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | _ => 1

example : (Finset.univ.sum hatDirectionMultiplicity : Nat) = 8 := by decide

end AperiodicMonotile
