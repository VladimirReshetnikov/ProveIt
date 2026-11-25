import IPRADerivations.Geometry.PlatonicSurface.Intrinsic
import IPRADerivations.Core.Tactic
import IPRADerivations.Core.LinearCombination

/-!
# The icosahedral strip minimum

Packet: `geometry/platonic_surface_diameters_2026-11-19`, the icosahedron (diameter `√7`). Imported from the
packet's `lean/IcosahedronIPRA.lean`: `cost_correct`, `signedBudget` (the two developed corner costs sum to
`504 A²B²` minus an explicit nonnegative slack) and `icoMinimum` (the least genuine cost is at most
`504 A²B²`, i.e. squared length at most `7`).
-/

namespace LeanProofs.IPRA.Geometry.PlatonicSurface.Icosahedron

open LeanProofs.ConciseIPRA LeanProofs.IPRA LeanProofs.IPRA.Geometry.PlatonicSurface
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.Probability.FiniteLaws (min_le_left min_le_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- In triangular coordinates multiplied by six. Source and destination weights
can have different masses, A=a+b+c and B=d+e+f. The first route is translated
by 18 in the second coordinate to make every input coordinate nonnegative. -/
def coords (first : Bool) (a b c d e f : PTm n) :
    PTm n × PTm n × PTm n × PTm n :=
  let A := a+b+c
  let B := d+e+f
  (A*(num 6*d + num 3*e + num 4*f),
   if first then A*(num 3*e+num 4*f) else A*(num 12*d+num 15*e+num 16*f),
   B*(num 3*b+num 2*c),
   if first then B*(num 18*A + num 2*c) else B*(num 2*c))

def signed (k : Bool) (a b c d e f : PTm n) : ZT n :=
  let (x,y,u,v) := coords k a b c d e f
  triQ (z x-z u) (z y-z v)

def cost (k : Bool) (a b c d e f : PTm n) : PTm n :=
  let (x,y,u,v) := coords k a b c d e f
  twiceSq x y u v

theorem cost_correct (k : Bool) (a b c d e f : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (z (cost k a b c d e f)) (z (num 2)*signed k a b c d e f) :=
  twiceSq_correct _ _ _ _

/-- Nine gaps from 504 in the sum of the two developed corner costs. -/
def cornerGap (a b c d e f : PTm n) : PTm n :=
  a*(num 36*e+num 12*f) + b*(num 36*d+num 54*e+num 48*f) +
    c*(num 12*d+num 48*e+num 48*f)

def shapeVar (a b c : PTm n) : PTm n :=
  num 9*a*b + num 12*a*c + num 3*b*c

def slack (a b c d e f : PTm n) : PTm n :=
  let A := a+b+c
  let B := d+e+f
  A*B*cornerGap a b c d e f +
    num 2*(B*B*shapeVar a b c + A*A*shapeVar d e f)

theorem signedBudget (a b c d e f : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (signed true a b c d e f + signed false a b c d e f +
       z (slack a b c d e f)) (z (num 504*clearance a b c d e f)) := by
  simp only [signed, coords, Bool.false_eq_true, if_true, if_false,
    triQ, slack, shapeVar, cornerGap, clearance, z]
  ipra_ring

/-- Minimum of the two genuine natural squared-distance costs. The scaling is
72 A²B², so the upper bound 504 A²B² states the geometric bound seven. -/
theorem icoMinimum (a b c d e f : PTm n) :
    Γ ⊢[PRAAx] le (least (cost true a b c d e f) (cost false a b c d e f))
      (num 504*clearance a b c d e f) := by
  let t := cost true a b c d e f
  let u := cost false a b c d e f
  let D := clearance a b c d e f
  have budget : Γ ⊢[PRAAx] le (t+u) (num 1008*D) := by
    refine le_of_eq_add (d := num 2*slack a b c d e f) ?_
    dsimp only [D, t, u]
    ipra_lc -2*ZT.toZ_eq (signedBudget (Γ := Γ) a b c d e f) - ZT.toZ_eq (cost_correct (Γ := Γ) true a b c d e f) -
      ZT.toZ_eq (cost_correct (Γ := Γ) false a b c d e f)
  have h := le_trans (add_le_add₂ (min_le_left t u) (min_le_right t u)) budget
  change Γ ⊢[PRAAx] le (least t u) (num 504*D)
  apply mul_le_cancel (d' := num 1)
  refine le_congr ?_ ?_ h <;> (try unfold least) <;> ipra_ring

end LeanProofs.IPRA.Geometry.PlatonicSurface.Icosahedron
