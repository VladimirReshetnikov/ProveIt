import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Unchecked scalar polynomial certificate; no graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N5R9LowerCertificate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem shifted_lower_certificate (u v : R) (hu : 0≤u) (hv : 0≤v) :
    let x := 32+u
    let t := 1+v
    let B := x^4+8*x^3+28*x^2+56*x
    let d := x*t^2+2
    let z := t*(x+1)+2
    let c := z^8-7*z^6+15*z^4-10*z^2+1
    let y5 := d^4-3*d^2+1
    0<(c-t*y5-2*y5)-x^4*t^8*(B+68-t) := by
  dsimp
  ring_nf
  positivity

#print axioms Trace74N5R9LowerCertificate.shifted_lower_certificate
end Trace74N5R9LowerCertificate
