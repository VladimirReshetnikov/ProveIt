import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Unchecked conditional ordered-ring estimates. No graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N5R7Growth
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem sixth_bound (x : R) (hx : 32≤x) : (x+2)^6≤2*x^6 := by
  have hu : 0≤x-32 := sub_nonneg.mpr hx
  have hs : ∀ u : R, 0≤u → 0≤2*(32+u)^6-((32+u)+2)^6 := by
    intro u hu'
    ring_nf
    positivity
  have hp := hs (x-32) hu
  have he : 32+(x-32)=x := by ring
  rw [he] at hp
  linarith

theorem squared_growth (x t : R) (hx : 32≤x) (ht : 2≤t)
    (hgap : t*((x*t^2+2)^4-3*(x*t^2+2)^2+1) <
      (t*(x+1)+2)^6-5*(t*(x+1)+2)^4+6*(t*(x+1)+2)^2-1) :
    t^3 < 2*x^2 := by
  have hx0 : 0<x := by linarith
  have ht0 : 0<t := by linarith
  let u := x*t^2
  let z := t*(x+1)+2
  have hu : 0≤u := by dsimp [u]; positivity
  have hz : 2≤z := by dsimp [z]; nlinarith
  have hlower : x^4*t^9 ≤ t*((x*t^2+2)^4-3*(x*t^2+2)^2+1) := by
    have hp : 0≤t*(8*u^3+21*u^2+20*u+5) := by positivity
    dsimp [u] at hp
    nlinarith [hp]
  have hz2 : 1≤z^2 := by nlinarith
  have hz2n : 0≤z^2-1 := sub_nonneg.mpr hz2
  have hz5 : 0≤5*z^2-1 := by nlinarith
  have hp : 0≤(z^2-1)*(5*z^2-1) := mul_nonneg hz2n hz5
  have hupper : z^6-5*z^4+6*z^2-1 ≤ z^6 := by nlinarith [hp]
  have hz0 : 0≤z := by linarith
  have hzbound : z≤t*(x+2) := by dsimp [z]; nlinarith
  have hpow : z^6≤(t*(x+2))^6 := pow_le_pow_left₀ hz0 hzbound 6
  have ht6 : 0≤t^6 := by positivity
  have hsixth := sixth_bound x hx
  have hm := mul_le_mul_of_nonneg_left hsixth ht6
  have hproduct : (t*(x+2))^6≤2*x^6*t^6 := by nlinarith [hm]
  have hh : x^4*t^9 < 2*x^6*t^6 := by
    dsimp [z] at hupper hpow
    nlinarith [hlower,hupper,hpow,hproduct]
  have hf : 0<x^4*t^6 := by positivity
  have hh' : (x^4*t^6)*t^3 < (x^4*t^6)*(2*x^2) := by nlinarith [hh]
  by_contra hn
  have hle : 2*x^2≤t^3 := le_of_not_gt hn
  have hm' := mul_le_mul_of_nonneg_left hle (le_of_lt hf)
  exact (not_lt_of_ge hm') hh'

theorem large_size (q x y : R) (hq : 1073741824≤q)
    (hx : 32≤x) (hy : q^3≤y) (hg : 4*y^3<x^2) :
    65532*(q-1)*y<x := by
  have hq0 : 0<q := by linarith
  have hh : 0≤q-1 := by linarith
  have hq2 : 0<q^2 := by positivity
  have hqcube : 0<q^3 := by positivity
  have hy0 : 0<y := lt_of_lt_of_le hqcube hy
  have hy2 : 0≤y^2 := by positivity
  have hsquare : (q-1)^2≤q^2 := by nlinarith
  have hmul : 4294443024*(q-1)^2≤4294443024*q^2 := by nlinarith [hsquare]
  have hconst : (4294443024:R)<4*q := by linarith
  have hmul2 := mul_lt_mul_of_pos_right hconst hq2
  have hsmall : 4294443024*(q-1)^2 < 4*y := by nlinarith [hmul,hmul2]
  have hh2 := mul_lt_mul_of_pos_right hsmall (show 0<y^2 by positivity)
  have ha : 0≤65532*(q-1)*y := by positivity
  by_contra hn
  have hle : x≤65532*(q-1)*y := le_of_not_gt hn
  nlinarith [hh2]

#print axioms Trace74N5R7Growth.sixth_bound
#print axioms Trace74N5R7Growth.squared_growth
#print axioms Trace74N5R7Growth.large_size
end Trace74N5R7Growth
