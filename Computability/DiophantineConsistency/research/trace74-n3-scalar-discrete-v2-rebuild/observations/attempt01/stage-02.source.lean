import Trace74N3UpperCertificate
import Mathlib.Tactic.Linarith

/-! UNCHECKED DRAFT. Instantiate the shifted upper certificate to the
third/fifth Pell ordinate polynomials. No graph binding is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N3UpperBound
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem upper_of_polynomials (x y : R) (hx : 32≤x)
    (hgap : (32*x^2*y^4+32*x*y^2+6)*y <
      16*(y*(x+1)+1)^4-12*(y*(x+1)+1)^2+1) :
    2*y < x*x+4*x+8 := by
  by_contra hn
  have hu : 0≤x-32 := sub_nonneg.mpr hx
  have hw : 0≤2*y-(x*x+4*x+8) := sub_nonneg.mpr (le_of_not_gt hn)
  have hh := Trace74N3UpperCertificate.shifted_upper_certificate
    (x-32) (2*y-(x*x+4*x+8)) hu hw
  dsimp at hh
  have hx' : 32+(x-32)=x := by ring
  rw [hx'] at hh
  have ht : x*x+4*x+8+(2*y-(x*x+4*x+8))=2*y := by ring
  rw [ht] at hh
  have hpoly : x*x*(2*y)^5+4*x*(2*y)^3+3*(2*y)-
      ((2*y)*(x+1)+2)^4+3*((2*y)*(x+1)+2)^2-1 =
      (32*x^2*y^4+32*x*y^2+6)*y-
        (16*(y*(x+1)+1)^4-12*(y*(x+1)+1)^2+1) := by ring
  rw [hpoly] at hh
  linarith

#print axioms Trace74N3UpperBound.upper_of_polynomials
end Trace74N3UpperBound
