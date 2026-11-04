import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Unchecked scalar polynomial certificate; no graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6R9LowerCertificate
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
theorem certificate (u w : R) (hu : 0≤u) (hw : 0≤w) :
    let x := 32+u
    let t := x+3+w
    let d := x*t^2+2
    let z := t*(x+1)+2
    let y6 := d^5-4*d^3+3*d
    let c := z^8-7*z^6+15*z^4-10*z^2+1
    0<t*y6-c := by
  dsimp
  ring_nf
  positivity
#print axioms Trace74N6R9LowerCertificate.certificate
end Trace74N6R9LowerCertificate
