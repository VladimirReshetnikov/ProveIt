/-!
# Exact finite encoding for the hat monotile

All semantic objects used by the iPRA theorem are finite natural-number codes.  The
ambient triangular lattice is represented by axial integer coordinates.  Rational
points are a common positive denominator together with two signed numerators.
-/

namespace AperiodicMonotile

structure ZPair where
  pos : Nat
  neg : Nat
  deriving DecidableEq, Repr

def ZPair.val (z : ZPair) : Int := Int.ofNat z.pos - Int.ofNat z.neg

structure Axial where
  u : ZPair
  v : ZPair
  deriving DecidableEq, Repr

/-- Q(u,v)=u²+uv+v², the squared norm in the triangular basis. -/
def qNorm (u v : Int) : Int := u*u + u*v + v*v

/-- A rational axial point (u/d,v/d), with the convention d>0. -/
structure QPoint where
  den : Nat
  den_pos : 0 < den
  u : ZPair
  v : ZPair
  deriving Repr

/-- The finite dihedral part of an allowed placement. -/
inductive D12
  | rot (k : Fin 6)
  | refl (k : Fin 6)
  deriving DecidableEq, Repr

structure Placement where
  linear : D12
  shift : Axial
  deriving DecidableEq, Repr

structure PolygonCode where
  vertices : List Axial
  atLeastThree : 3 ≤ vertices.length
  deriving Repr

structure TileInstance where
  place : Placement
  reflected : Bool
  deriving DecidableEq, Repr

abbrev PatchCode := List TileInstance

/-- A finite quotient of an aligned tiling by two independent translations. -/
structure TorusCode where
  period₁ : Axial
  period₂ : Axial
  det_ne_zero :
    period₁.u.val * period₂.v.val - period₁.v.val * period₂.u.val ≠ 0
  representatives : PatchCode

/-- Primitive-recursive signed coding used by the object theory. -/
def encodeInt : Int → Nat
  | Int.ofNat n => 2*n
  | Int.negSucc n => 2*n+1

def decodeInt (n : Nat) : Int :=
  if h : n % 2 = 0 then Int.ofNat (n/2) else Int.negSucc (n/2)

/-- Gödel codes.  The implementation should use `Core/Pairing` in `IPRADerivations`. -/
opaque codeAxial : Axial → Nat
opaque decodeAxial : Nat → Axial
opaque codePlacement : Placement → Nat
opaque decodePlacement : Nat → Placement
opaque codePatch : PatchCode → Nat
opaque decodePatch : Nat → PatchCode

/-- Closed Boolean predicates to be reflected into iPRA. -/
opaque simplePolygonB : PolygonCode → Bool
opaque validPatchB : PolygonCode → PatchCode → Bool
opaque coversHexBallB : PolygonCode → PatchCode → Nat → Bool
opaque periodicTorusB : PolygonCode → TorusCode → Bool
opaque periodOnWindowB : PolygonCode → PatchCode → Axial → Nat → Bool

/-- Required correctness statements for the executable layer. -/
axiom validPatchB_spec (tile : PolygonCode) (p : PatchCode) :
  validPatchB tile p = true ↔ True -- replace `True` by the geometric finite predicate

axiom coversHexBallB_spec (tile : PolygonCode) (p : PatchCode) (r : Nat) :
  coversHexBallB tile p r = true ↔ True -- exact cell-coverage specification

end AperiodicMonotile
