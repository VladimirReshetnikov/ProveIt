import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-! Unchecked univariate positivity certificates; no graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6R11CompactBase
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
def B (x : R) : R := x^5+10*x^4+45*x^3+120*x^2+210*x
def C (a : R) : R := 11+220*a+1287*a^2+3432*a^3+5005*a^4+
  4368*a^5+2380*a^6+816*a^7+171*a^8+20*a^9
theorem base (u : R) (hu : 0≤u) :
    let x := 32+u
    let T := B x+260
    let a := x+1
    0<x^5*T-a^10 ∧ 0<(x^5*T-a^10)*T-C a := by
  dsimp [B,C]
  constructor <;> ring_nf <;> positivity
#print axioms Trace74N6R11CompactBase.base
end Trace74N6R11CompactBase
