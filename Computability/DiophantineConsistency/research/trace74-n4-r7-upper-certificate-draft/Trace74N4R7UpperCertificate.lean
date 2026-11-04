import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! UNCHECKED DRAFT. Shifted generic polynomial positivity for the n4/r7
upper interval endpoint; no graph binding or exclusion is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4R7UpperCertificate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem shifted_upper_certificate (u w : R) (hu : 0≤u) (hw : 0≤w) :
    let x := 32+u
    let t := x^3+6*x^2+15*x+22+w
    let z := t*(x+1)+2
    0 < x^3*t^7+6*x^2*t^5+10*x*t^3+4*t-z^6+5*z^4-6*z^2+1 := by
  dsimp
  ring_nf
  positivity

#print axioms Trace74N4R7UpperCertificate.shifted_upper_certificate
end Trace74N4R7UpperCertificate
