import Trace74N4R7UpperCertificate
import Mathlib.Tactic.Linarith

/-! UNCHECKED DRAFT. Instantiate the shifted n4/r7 upper endpoint
certificate; no graph binding or index exclusion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4R7UpperBound
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem upper_of_polynomials (x t : R) (hx : 32≤x)
    (hgap : x^3*t^7+6*x^2*t^5+10*x*t^3+4*t <
      (t*(x+1)+2)^6-5*(t*(x+1)+2)^4+6*(t*(x+1)+2)^2-1) :
    t < x^3+6*x^2+15*x+22 := by
  by_contra hn
  have hu : 0≤x-32 := sub_nonneg.mpr hx
  have hw : 0≤t-(x^3+6*x^2+15*x+22) := sub_nonneg.mpr (le_of_not_gt hn)
  have hh := Trace74N4R7UpperCertificate.shifted_upper_certificate
    (x-32) (t-(x^3+6*x^2+15*x+22)) hu hw
  dsimp at hh
  have hx' : 32+(x-32)=x := by ring
  rw [hx'] at hh
  have ht : x^3+6*x^2+15*x+22+(t-(x^3+6*x^2+15*x+22))=t := by ring
  rw [ht] at hh
  linarith

#print axioms Trace74N4R7UpperBound.upper_of_polynomials
end Trace74N4R7UpperBound
