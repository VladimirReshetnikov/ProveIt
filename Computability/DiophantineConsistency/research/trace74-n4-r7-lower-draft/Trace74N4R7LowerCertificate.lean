import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Unchecked scalar polynomial certificate; no graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4R7LowerCertificate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem shifted_lower_certificate (u v : R) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    let x := 32+u
    let t := 1+v
    let B := x^3+6*x^2+15*x
    let z := t*(x+1)+2
    let c := z^6-5*z^4+6*z^2-1
    let ky := x^3*t^7+6*x^2*t^5+10*x*t^3+4*t
    let k := 2*x^3*t^6+12*x^2*t^4+20*x*t^2+8
    0 < (c-ky-k)-x^3*t^6*(B+18-t) := by
  dsimp
  ring_nf
  positivity

#print axioms Trace74N4R7LowerCertificate.shifted_lower_certificate
end Trace74N4R7LowerCertificate
