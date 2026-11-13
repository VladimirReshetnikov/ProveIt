import Trace74N4R7LowerBound
import Trace74N4R7UpperBound

/-! Unchecked scalar endpoint join; no graph binding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N4R7ScalarDiscrete
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

def c (x t : R) : R := (t*(x+1)+2)^6-5*(t*(x+1)+2)^4+6*(t*(x+1)+2)^2-1
def ky (x t : R) : R := x^3*t^7+6*x^2*t^5+10*x*t^3+4*t
def k (x t : R) : R := 2*x^3*t^6+12*x^2*t^4+20*x*t^2+8

theorem no_scalar_solution (q x Y w s : R)
    (hdisc : ∀ z : R, 0<z → 1≤z) (hq : 32≤q) (hx : 32≤x) (hY : 1≤Y)
    (hxq : x=q*w) (hYq : Y=q^3*s)
    (hlo : ky x (2*Y)<c x (2*Y))
    (hhi : c x (2*Y)<ky x (2*Y)+k x (2*Y)) : False := by
  have ht : (1:R) ≤ 2*Y := by linarith
  have hleft : x^3+6*x^2+15*x+18<2*Y := by
    exact Trace74N4R7LowerBound.lower_of_polynomials x (2*Y) hx ht hhi
  have hright : 2*Y<x^3+6*x^2+15*x+22 := by
    exact Trace74N4R7UpperBound.upper_of_polynomials x (2*Y) hx hlo
  let Z : R := 2*Y-x^3-6*x^2-15*x
  let T : R := 2*q^2*s-q^2*w^3-6*q*w^2-15*w
  have hZ : Z=q*T := by dsimp [Z,T]; rw [hxq,hYq]; ring
  have hqpos : 0<q := lt_of_lt_of_le (by norm_num : (0:R)<32) hq
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

#print axioms Trace74N4R7ScalarDiscrete.no_scalar_solution
end Trace74N4R7ScalarDiscrete
