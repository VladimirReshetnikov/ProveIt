import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! UNCHECKED DRAFT. A subtraction-free shifted certificate for the upper
n=3 interval endpoint. It does not bind the constants to a graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N3UpperCertificate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem shifted_upper_certificate (u w : R) (hu : 0≤u) (hw : 0≤w) :
    let x := 32+u
    let t := x*x+4*x+8+w
    let a := t*(x+1)+2
    0 < x*x*t^5+4*x*t^3+3*t-a^4+3*a^2-1 := by
  dsimp
  ring_nf
  positivity

#print axioms Trace74N3UpperCertificate.shifted_upper_certificate
end Trace74N3UpperCertificate
