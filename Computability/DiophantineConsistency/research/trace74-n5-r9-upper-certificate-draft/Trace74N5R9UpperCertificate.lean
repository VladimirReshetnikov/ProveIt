import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! UNCHECKED DRAFT. Shifted polynomial positivity for the n5/r9 upper
interval endpoint. No graph or index exclusion is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N5R9UpperCertificate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem shifted_upper_certificate (u w : R) (hu : 0≤u) (hw : 0≤w) :
    let x := 32+u
    let t := x^4+8*x^3+28*x^2+56*x+73+w
    let z := t*(x+1)+2
    let d := x*t^2+2
    0 < t*(d^4-3*d^2+1)-(z^8-7*z^6+15*z^4-10*z^2+1) := by
  dsimp
  ring_nf
  positivity

#print axioms Trace74N5R9UpperCertificate.shifted_upper_certificate
end Trace74N5R9UpperCertificate
