import Trace74N4R7LowerCertificate
import Mathlib.Tactic.Linarith

/-! Unchecked conditional lower endpoint, independent of any graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4R7LowerBound
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem lower_of_polynomials (x t : R) (hx : 32 ≤ x) (ht : 1 ≤ t)
    (hgap : (t*(x+1)+2)^6-5*(t*(x+1)+2)^4+6*(t*(x+1)+2)^2-1 <
      (x^3*t^7+6*x^2*t^5+10*x*t^3+4*t)+
      (2*x^3*t^6+12*x^2*t^4+20*x*t^2+8)) :
    x^3+6*x^2+15*x+18 < t := by
  by_contra hn
  have hu : 0 ≤ x-32 := sub_nonneg.mpr hx
  have hv : 0 ≤ t-1 := sub_nonneg.mpr ht
  have hc := Trace74N4R7LowerCertificate.shifted_lower_certificate (x-32) (t-1) hu hv
  dsimp at hc
  have hx' : 32+(x-32)=x := by ring
  have ht' : 1+(t-1)=t := by ring
  rw [hx',ht'] at hc
  have hdiff : 0 ≤ x^3+6*x^2+15*x+18-t := sub_nonneg.mpr (le_of_not_gt hn)
  have hx0 : 0 ≤ x := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hp : 0 ≤ x^3*t^6*(x^3+6*x^2+15*x+18-t) := by positivity
  linarith

#print axioms Trace74N4R7LowerBound.lower_of_polynomials
end Trace74N4R7LowerBound
