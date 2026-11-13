import Trace74N6R11LowerCertificate
import Trace74N6R11UpperCertificate
import Mathlib.Tactic.Linarith
/-! Unchecked conditional scalar obstruction in a discrete ordered ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6R11Scalar
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
def c (x t : R) : R := (t*(x+1)+2)^10-9*(t*(x+1)+2)^8+
  28*(t*(x+1)+2)^6-35*(t*(x+1)+2)^4+15*(t*(x+1)+2)^2-1
def y6 (x t : R) : R := (x*t^2+2)^5-4*(x*t^2+2)^3+3*(x*t^2+2)

theorem no_scalar_solution (q x Y w s : R)
    (hdisc : ∀z : R,0<z → 1≤z) (hq : 260≤q) (hx : 32≤x) (hY : 1≤Y)
    (hxq : x=q*w) (hYq : Y=q^3*s)
    (hlo : (2*Y)*y6 x (2*Y)<c x (2*Y))
    (hhi : c x (2*Y)<(2*Y)*y6 x (2*Y)+2*y6 x (2*Y)) : False := by
  let t : R := 2*Y
  let B : R := x^5+10*x^4+45*x^3+120*x^2+210*x
  have ht : 1≤t := by dsimp [t]; linarith
  have hleft : B+250<t := by
    by_contra hn
    have hu : 0≤x-32 := sub_nonneg.mpr hx
    have hv : 0≤t-1 := sub_nonneg.mpr ht
    have hc := Trace74N6R11LowerCertificate.certificate (x-32) (t-1) hu hv
    dsimp at hc
    have hx' : 32+(x-32)=x := by ring
    have ht' : 1+(t-1)=t := by ring
    rw [hx',ht'] at hc
    have hdiff : 0≤B+250-t := sub_nonneg.mpr (le_of_not_gt hn)
    have hx0 : 0≤x := by linarith
    have ht0 : 0≤t := by linarith
    have hp : 0≤x^5*t^10*(B+250-t) := by positivity
    dsimp [B] at hdiff hp
    dsimp [c,y6] at hhi
    change (t*(x+1)+2)^10-9*(t*(x+1)+2)^8+28*(t*(x+1)+2)^6-
      35*(t*(x+1)+2)^4+15*(t*(x+1)+2)^2-1 <
      t*((x*t^2+2)^5-4*(x*t^2+2)^3+3*(x*t^2+2))+
      2*((x*t^2+2)^5-4*(x*t^2+2)^3+3*(x*t^2+2)) at hhi
    linarith
  have hright : t<B+260 := by
    by_contra hn
    have hu : 0≤x-32 := sub_nonneg.mpr hx
    have hw : 0≤t-(B+260) := sub_nonneg.mpr (le_of_not_gt hn)
    have hc := Trace74N6R11UpperCertificate.certificate (x-32) (t-(B+260)) hu hw
    dsimp at hc
    have hx' : 32+(x-32)=x := by ring
    rw [hx'] at hc
    have ht' : x^5+10*x^4+45*x^3+120*x^2+210*x+260+(t-(B+260))=t := by dsimp [B]; ring
    rw [ht'] at hc
    dsimp [c,y6] at hlo
    change t*((x*t^2+2)^5-4*(x*t^2+2)^3+3*(x*t^2+2)) <
      (t*(x+1)+2)^10-9*(t*(x+1)+2)^8+28*(t*(x+1)+2)^6-
      35*(t*(x+1)+2)^4+15*(t*(x+1)+2)^2-1 at hlo
    linarith
  let Z : R := t-B
  let T : R := 2*q^2*s-q^4*w^5-10*q^3*w^4-45*q^2*w^3-120*q*w^2-210*w
  have hZ : Z=q*T := by dsimp [Z,T,t,B]; rw [hxq,hYq]; ring
  have hqpos : 0<q := lt_of_lt_of_le (by norm_num : (0:R)<260) hq
  have hZpos : 0<Z := by dsimp [Z]; linarith
  have hZq : Z<q := by dsimp [Z]; linarith
  have hTpos : 0<T := by
    by_contra hn
    have hh : q*T≤0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hqpos) (le_of_not_gt hn)
    rw [←hZ] at hh
    exact (not_le_of_gt hZpos) hh
  have hqZ : q≤Z := by
    have hh := mul_le_mul_of_nonneg_left (hdisc T hTpos) (le_of_lt hqpos)
    simpa only [mul_one,←hZ] using hh
  exact (not_le_of_gt hZq) hqZ
#print axioms Trace74N6R11Scalar.no_scalar_solution
end Trace74N6R11Scalar
