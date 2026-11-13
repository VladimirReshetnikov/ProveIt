import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-! Unchecked scalar polynomial certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6R11LowerCertificate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
theorem certificate (u v : R) (hu : 0≤u) (hv : 0≤v) :
    let x := 32+u
    let t := 1+v
    let B := x^5+10*x^4+45*x^3+120*x^2+210*x
    let d := x*t^2+2
    let z := t*(x+1)+2
    let y6 := d^5-4*d^3+3*d
    let c := z^10-9*z^8+28*z^6-35*z^4+15*z^2-1
    0<(c-t*y6-2*y6)-x^5*t^10*(B+250-t) := by
  dsimp
  ring_nf
  positivity
#print axioms Trace74N6R11LowerCertificate.certificate
end Trace74N6R11LowerCertificate
