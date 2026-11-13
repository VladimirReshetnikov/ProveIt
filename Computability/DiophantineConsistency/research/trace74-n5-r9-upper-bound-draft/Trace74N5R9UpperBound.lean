import Trace74N5R9UpperCertificate
import Mathlib.Tactic.Linarith

/-! UNCHECKED DRAFT. Instantiate the n5/r9 upper endpoint certificate;
no graph binding or index exclusion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N5R9UpperBound
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem upper_of_polynomials (x t : R) (hx : 32≤x)
    (hgap : t*((x*t^2+2)^4-3*(x*t^2+2)^2+1) <
      (t*(x+1)+2)^8-7*(t*(x+1)+2)^6+15*(t*(x+1)+2)^4-10*(t*(x+1)+2)^2+1) :
    t < x^4+8*x^3+28*x^2+56*x+73 := by
  by_contra hn
  have hu : 0≤x-32 := sub_nonneg.mpr hx
  have hw : 0≤t-(x^4+8*x^3+28*x^2+56*x+73) := sub_nonneg.mpr (le_of_not_gt hn)
  have hh := Trace74N5R9UpperCertificate.shifted_upper_certificate
    (x-32) (t-(x^4+8*x^3+28*x^2+56*x+73)) hu hw
  dsimp at hh
  have hx' : 32+(x-32)=x := by ring
  rw [hx'] at hh
  have ht : x^4+8*x^3+28*x^2+56*x+73+(t-(x^4+8*x^3+28*x^2+56*x+73))=t := by ring
  rw [ht] at hh
  linarith

#print axioms Trace74N5R9UpperBound.upper_of_polynomials
end Trace74N5R9UpperBound
