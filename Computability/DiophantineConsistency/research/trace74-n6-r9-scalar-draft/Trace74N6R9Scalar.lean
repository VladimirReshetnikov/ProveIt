import Trace74N6R9LowerCertificate
import Trace74N6R9UpperCertificate
import Mathlib.Tactic.Linarith

/-! Unchecked scalar contradiction in a discrete ordered ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6R9Scalar
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
def c (x t : R) : R := (t*(x+1)+2)^8-7*(t*(x+1)+2)^6+
  15*(t*(x+1)+2)^4-10*(t*(x+1)+2)^2+1
def y6 (x t : R) : R := (x*t^2+2)^5-4*(x*t^2+2)^3+3*(x*t^2+2)

theorem no_scalar_solution (x t : R)
    (hdisc : ∀z : R,0<z → 1≤z) (hx : 32≤x) (ht : 2≤t)
    (hlo : t*y6 x t<c x t) (hhi : c x t<t*y6 x t+2*y6 x t) : False := by
  have hleft : t-3<x := by
    by_contra hn
    have hu : 0≤x-32 := sub_nonneg.mpr hx
    have hw : 0≤t-x-3 := by linarith
    have hc := Trace74N6R9LowerCertificate.certificate (x-32) (t-x-3) hu hw
    dsimp at hc
    have hx' : 32+(x-32)=x := by ring
    rw [hx'] at hc
    have ht' : x+3+(t-x-3)=t := by ring
    rw [ht'] at hc
    dsimp [c,y6] at hlo
    linarith
  have hright : x<t-2 := by
    by_contra hn
    have hu : 0≤t-2 := sub_nonneg.mpr ht
    have hw : 0≤x-(t-2) := sub_nonneg.mpr (le_of_not_gt hn)
    have hc := Trace74N6R9UpperCertificate.certificate (t-2) (x-(t-2)) hu hw
    dsimp at hc
    have ht' : 2+(t-2)=t := by ring
    have hx' : (t-2)+(x-(t-2))=x := by ring
    rw [ht',hx'] at hc
    dsimp [c,y6] at hhi
    linarith
  have hz : 0<x-(t-3) := by linarith
  have hh := hdisc (x-(t-3)) hz
  linarith

#print axioms Trace74N6R9Scalar.no_scalar_solution
end Trace74N6R9Scalar
