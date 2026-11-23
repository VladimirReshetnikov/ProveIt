import EuclideanIPRA.Derivations
import IPRADerivations.Core.Definitions

/-!
# Exact geometry syntax and the missing algebraic-code backend

STATUS: definition/target outline, NOT compiled in this environment.

`AlgebraicSymbols` requires actual primitive-recursive program syntax (`PR k`),
not arbitrary Lean functions.  No value of this structure is supplied here:
implementing and verifying the complete real-algebraic backend is an explicitly
listed remaining task.  The root/sign/field laws are NOT assumed as axioms.

Once a fixed backend has been constructed, every expression below is a literal
first-order iPRA term, and every specification is a literal first-order formula.
This avoids any assertion that evaluation of an arbitrary coded PR program is
itself primitive recursive.  The metatheoretic construction is uniform on
syntax; an individual output theorem uses the finitely many fixed programs
appearing in it.
-/

namespace EuclideanIPRA.Syntax

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

/-- The fixed programs required from a finite real-algebraic presentation.
Boolean programs return exactly 0 or 1; invalid-input behavior is totalized.
`root` returns the nonnegative square root on nonnegative valid inputs.
`inverse` returns any fixed default on zero or invalid inputs.
-/
structure AlgebraicSymbols where
  valid : PR 1
  equal : PR 2
  less : PR 2
  zeroCode : PR 0
  oneCode : PR 0
  plus : PR 2
  opposite : PR 1
  times : PR 2
  inverse : PR 1
  root : PR 1

abbrev APoint (n : ℕ) := PTm n × PTm n

namespace AlgebraicSymbols

variable (S : AlgebraicSymbols) {n : ℕ}

def zero : PTm n := PTm.app S.zeroCode Fin.elim0
def one : PTm n := PTm.app S.oneCode Fin.elim0
def add (x y : PTm n) : PTm n := ap2 S.plus x y
def neg (x : PTm n) : PTm n := ap1 S.opposite x
def sub (x y : PTm n) : PTm n := S.add x (S.neg y)
def mul (x y : PTm n) : PTm n := ap2 S.times x y
def inv (x : PTm n) : PTm n := ap1 S.inverse x
def div (x y : PTm n) : PTm n := S.mul x (S.inv y)
def sqrt (x : PTm n) : PTm n := ap1 S.root x
def sq (x : PTm n) : PTm n := S.mul x x
def numeral : ℕ → PTm n
  | 0 => S.zero
  | k+1 => S.add (S.numeral k) S.one

def validF (x : PTm n) : Fm PTm n := ap1 S.valid x ≐ PTm.num 1
def eqF (x y : PTm n) : Fm PTm n := ap2 S.equal x y ≐ PTm.num 1
def apartF (x y : PTm n) : Fm PTm n := ap2 S.equal x y ≐ PTm.zero
def ltF (x y : PTm n) : Fm PTm n := ap2 S.less x y ≐ PTm.num 1
def leF (x y : PTm n) : Fm PTm n := S.ltF x y ⋎ S.eqF x y

def pointValid (p : APoint n) : Fm PTm n := S.validF p.1 ⋏ S.validF p.2
def pointEq (p q : APoint n) : Fm PTm n := S.eqF p.1 q.1 ⋏ S.eqF p.2 q.2
def pointAdd (p q : APoint n) : APoint n := (S.add p.1 q.1, S.add p.2 q.2)
def pointSub (p q : APoint n) : APoint n := (S.sub p.1 q.1, S.sub p.2 q.2)
def scale (t : PTm n) (p : APoint n) : APoint n := (S.mul t p.1, S.mul t p.2)
def turn (p : APoint n) : APoint n := (S.neg p.2, p.1)
def dot (p q : APoint n) : PTm n := S.add (S.mul p.1 q.1) (S.mul p.2 q.2)
def det (p q : APoint n) : PTm n := S.sub (S.mul p.1 q.2) (S.mul p.2 q.1)
def sqnorm (p : APoint n) : PTm n := S.add (S.sq p.1) (S.sq p.2)
def sqdist (p q : APoint n) : PTm n := S.sqnorm (S.pointSub p q)
def length (p q : APoint n) : PTm n := S.sqrt (S.sqdist p q)
def area2 (a b c : APoint n) : PTm n := S.det (S.pointSub b a) (S.pointSub c a)

def collinear (a b c : APoint n) : Fm PTm n := S.eqF (S.area2 a b c) S.zero
def ccw (a b c : APoint n) : Fm PTm n := S.ltF S.zero (S.area2 a b c)
def noncollinear (a b c : APoint n) : Fm PTm n := S.apartF (S.area2 a b c) S.zero
def distinct (a b : APoint n) : Fm PTm n := S.ltF S.zero (S.sqdist a b)
def between (a p b : APoint n) : Fm PTm n :=
  S.collinear a p b ⋏ S.leF (S.dot (S.pointSub p a) (S.pointSub p b)) S.zero
def rightAngle (a p b : APoint n) : Fm PTm n :=
  S.distinct a p ⋏ S.distinct b p ⋏
    S.eqF (S.dot (S.pointSub a p) (S.pointSub b p)) S.zero
def perpendicular (u v : APoint n) : Fm PTm n := S.eqF (S.dot u v) S.zero
def parallel (u v : APoint n) : Fm PTm n := S.eqF (S.det u v) S.zero
def onLine (p a u : APoint n) : Fm PTm n := S.eqF (S.det (S.pointSub p a) u) S.zero
def onCircle (p o : APoint n) (r : PTm n) : Fm PTm n := S.eqF (S.sqdist p o) (S.sq r)

/-- Cosine and squared sine of a nondegenerate interior angle.
No transcendental inverse-trigonometric function is used.
-/
def cosine (u v : APoint n) : PTm n :=
  S.div (S.dot u v) (S.mul (S.sqrt (S.sqnorm u)) (S.sqrt (S.sqnorm v)))
def sineSquared (u v : APoint n) : PTm n :=
  S.div (S.sq (S.det u v)) (S.mul (S.sqnorm u) (S.sqnorm v))
def angleEq (u v u' v' : APoint n) : Fm PTm n :=
  S.eqF (S.cosine u v) (S.cosine u' v')

/-! ## Explicit witnesses for the geometric constructions -/

def midpoint (a b : APoint n) : APoint n :=
  S.scale (S.inv (S.numeral 2)) (S.pointAdd a b)

def centroid (a b c : APoint n) : APoint n :=
  S.scale (S.inv (S.numeral 3)) (S.pointAdd (S.pointAdd a b) c)

def lineMeet (a u b v : APoint n) : APoint n :=
  S.pointAdd a (S.scale (S.div (S.det (S.pointSub b a) v) (S.det u v)) u)

def perpendicularFoot (p a u : APoint n) : APoint n :=
  S.pointAdd a (S.scale (S.div (S.dot (S.pointSub p a) u) (S.sqnorm u)) u)

def reflection (p a u : APoint n) : APoint n :=
  S.pointSub (S.scale (S.numeral 2) (S.perpendicularFoot p a u)) p

def circumcenter (a b c : APoint n) : APoint n :=
  let u := S.pointSub b a
  let v := S.pointSub c a
  let numerator := S.pointSub (S.scale (S.sqnorm v) (S.turn u))
    (S.scale (S.sqnorm u) (S.turn v))
  S.pointAdd a (S.scale (S.inv (S.mul (S.numeral 2) (S.det u v))) numerator)

def orthocenter (a b c : APoint n) : APoint n :=
  S.pointSub (S.pointAdd (S.pointAdd a b) c)
    (S.scale (S.numeral 2) (S.circumcenter a b c))

def incenter (a b c : APoint n) : APoint n :=
  let x := S.length b c
  let y := S.length c a
  let z := S.length a b
  S.scale (S.inv (S.add (S.add x y) z))
    (S.pointAdd (S.pointAdd (S.scale x a) (S.scale y b)) (S.scale z c))

def lineCircleDelta (p u o : APoint n) (r : PTm n) : PTm n :=
  S.sub (S.sq (S.dot (S.pointSub p o) u))
    (S.mul (S.sqnorm u) (S.sub (S.sqdist p o) (S.sq r)))

def lineCirclePlus (p u o : APoint n) (r : PTm n) : APoint n :=
  let t := S.div (S.add (S.neg (S.dot (S.pointSub p o) u))
    (S.sqrt (S.lineCircleDelta p u o r))) (S.sqnorm u)
  S.pointAdd p (S.scale t u)

def lineCircleMinus (p u o : APoint n) (r : PTm n) : APoint n :=
  let t := S.div (S.sub (S.neg (S.dot (S.pointSub p o) u))
    (S.sqrt (S.lineCircleDelta p u o r))) (S.sqnorm u)
  S.pointAdd p (S.scale t u)

def inversion (p o : APoint n) (r : PTm n) : APoint n :=
  S.pointAdd o (S.scale (S.div (S.sq r) (S.sqdist p o)) (S.pointSub p o))

/-! ## Concrete target formulas, not claimed theorems -/

def lineMeetSpec (a u b v : APoint n) : Fm PTm n :=
  (S.pointValid a ⋏ S.pointValid u ⋏ S.pointValid b ⋏ S.pointValid v ⋏
    S.apartF (S.det u v) S.zero) ⟶
  (S.onLine (S.lineMeet a u b v) a u ⋏ S.onLine (S.lineMeet a u b v) b v)

def circumcenterSpec (a b c : APoint n) : Fm PTm n :=
  (S.pointValid a ⋏ S.pointValid b ⋏ S.pointValid c ⋏ S.noncollinear a b c) ⟶
  (S.eqF (S.sqdist (S.circumcenter a b c) a) (S.sqdist (S.circumcenter a b c) b) ⋏
    S.eqF (S.sqdist (S.circumcenter a b c) a) (S.sqdist (S.circumcenter a b c) c))

def thalesSpec (a b p : APoint n) : Fm PTm n :=
  (S.pointValid a ⋏ S.pointValid b ⋏ S.pointValid p ⋏ S.distinct a b) ⟶
  Fm.iff
    (S.eqF (S.dot (S.pointSub p a) (S.pointSub p b)) S.zero)
    (S.eqF (S.sqdist p (S.midpoint a b))
      (S.div (S.sqdist a b) (S.numeral 4)))

def lineCircleSpec (p u o : APoint n) (r : PTm n) : Fm PTm n :=
  (S.pointValid p ⋏ S.pointValid u ⋏ S.pointValid o ⋏ S.validF r ⋏
    S.ltF S.zero (S.sqnorm u) ⋏ S.leF S.zero r ⋏
    S.leF S.zero (S.lineCircleDelta p u o r)) ⟶
  (S.onLine (S.lineCirclePlus p u o r) p u ⋏
    S.onCircle (S.lineCirclePlus p u o r) o r ⋏
    S.onLine (S.lineCircleMinus p u o r) p u ⋏
    S.onCircle (S.lineCircleMinus p u o r) o r)

def ptolemyInequalitySpec (a b c d : APoint n) : Fm PTm n :=
  (S.pointValid a ⋏ S.pointValid b ⋏ S.pointValid c ⋏ S.pointValid d) ⟶
  S.leF (S.mul (S.length a c) (S.length b d))
    (S.add (S.mul (S.length a b) (S.length c d))
      (S.mul (S.length a d) (S.length b c)))

end AlgebraicSymbols

end EuclideanIPRA.Syntax
