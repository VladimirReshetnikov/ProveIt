import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
/-! Unchecked conditional ordered-ring growth; no graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74AtLeastSevenR9Growth
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem eighth_bound (x : R) (hx : 32≤x) : (x+2)^8≤2*x^8 := by
  have hu : 0≤x-32 := sub_nonneg.mpr hx
  have hs : ∀ u : R, 0≤u → 0≤2*(32+u)^8-((32+u)+2)^8 := by
    intro u hu'
    ring_nf
    positivity
  have hp := hs (x-32) hu
  have he : 32+(x-32)=x := by ring
  rw [he] at hp
  linarith

theorem squared_growth (x t : R) (hx : 32≤x) (ht : 2≤t)
    (hgap : t*((x*t^2+2)^6-5*(x*t^2+2)^4+6*(x*t^2+2)^2-1) <
      (t*(x+1)+2)^8-7*(t*(x+1)+2)^6+15*(t*(x+1)+2)^4-
        10*(t*(x+1)+2)^2+1) : t^5<2*x^2 := by
  have hx0 : 0<x := by linarith
  have ht0 : 0<t := by linarith
  let u := x*t^2
  let z := t*(x+1)+2
  have hu : 0≤u := by dsimp [u]; positivity
  have hz : 2≤z := by dsimp [z]; nlinarith
  have hlower : x^6*t^13 ≤ t*((x*t^2+2)^6-5*(x*t^2+2)^4+6*(x*t^2+2)^2-1) := by
    have hp : 0≤t*(12*u^5+55*u^4+120*u^3+126*u^2+56*u+7) := by positivity
    calc
      x^6*t^13 ≤ x^6*t^13+t*(12*u^5+55*u^4+120*u^3+126*u^2+56*u+7) := le_add_of_nonneg_right hp
      _=t*((x*t^2+2)^6-5*(x*t^2+2)^4+6*(x*t^2+2)^2-1) := by dsimp [u]; ring
  have hz2 : 1≤z^2 := by nlinarith
  have hz2n : 0≤z^2-1 := sub_nonneg.mpr hz2
  have hz7 : 0≤7*z^2-1 := by nlinarith
  have hp : 0≤(z^2-1)*((z^2-1)*(7*z^2-1)+1)+1 := by positivity
  have hupper : z^8-7*z^6+15*z^4-10*z^2+1≤z^8 := by nlinarith [hp]
  have hz0 : 0≤z := by linarith
  have hzbound : z≤t*(x+2) := by dsimp [z]; nlinarith
  have hpow : z^8≤(t*(x+2))^8 := pow_le_pow_left₀ hz0 hzbound 8
  have ht8 : 0≤t^8 := by positivity
  have hm := mul_le_mul_of_nonneg_left (eighth_bound x hx) ht8
  have hproduct : (t*(x+2))^8≤2*x^8*t^8 := by
    calc
      (t*(x+2))^8=t^8*(x+2)^8 := by ring
      _≤t^8*(2*x^8) := hm
      _=2*x^8*t^8 := by ring
  have hh : x^6*t^13<2*x^8*t^8 := by
    have hgap' : t*((x*t^2+2)^6-5*(x*t^2+2)^4+6*(x*t^2+2)^2-1) <
        z^8-7*z^6+15*z^4-10*z^2+1 := by simpa only [z] using hgap
    exact lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le
      (lt_of_le_of_lt hlower hgap') hupper) hpow) hproduct
  have hf : 0<x^6*t^8 := by positivity
  have hh' : (x^6*t^8)*t^5 < (x^6*t^8)*(2*x^2) := by
    have h1 : (x^6*t^8)*t^5=x^6*t^13 := by ring
    have h2 : (x^6*t^8)*(2*x^2)=2*x^8*t^8 := by ring
    rw [h1,h2]
    exact hh
  by_contra hn
  have hle : 2*x^2≤t^5 := le_of_not_gt hn
  have hm' := mul_le_mul_of_nonneg_left hle (le_of_lt hf)
  exact (not_lt_of_ge hm') hh'

theorem large_size (q x y : R) (hq : 64≤q)
    (hx : 32≤x) (hy : q^3≤y) (hg : 16*y^5<x^2) :
    1048572*(q-1)*y<x := by
  have hq0 : 0<q := by linarith
  have hh : 0≤q-1 := by linarith
  have hq2 : 0<q^2 := by positivity
  have hqcube : 0<q^3 := by positivity
  have hy0 : 0<y := lt_of_lt_of_le hqcube hy
  have hsquare : (q-1)^2≤q^2 := by nlinarith
  have hmul : 1099503239184*(q-1)^2≤1099503239184*q^2 := by nlinarith [hsquare]
  have hq7 : (1099503239184:R)<16*q^7 := by
    have hh7 := pow_le_pow_left₀ (show (0:R)≤64 by norm_num) hq 7
    nlinarith [hh7]
  have hq9 := mul_lt_mul_of_pos_right hq7 hq2
  have hy3 := pow_le_pow_left₀ (show (0:R)≤q^3 by positivity) hy 3
  have hsmall : 1099503239184*(q-1)^2 < 16*y^3 := by nlinarith [hmul,hq9,hy3]
  have hh2 := mul_lt_mul_of_pos_right hsmall (show 0<y^2 by positivity)
  have ha : 0≤1048572*(q-1)*y := by positivity
  by_contra hn
  have hle : x≤1048572*(q-1)*y := le_of_not_gt hn
  nlinarith [hh2]

#print axioms Trace74AtLeastSevenR9Growth.eighth_bound
#print axioms Trace74AtLeastSevenR9Growth.squared_growth
#print axioms Trace74AtLeastSevenR9Growth.large_size
end Trace74AtLeastSevenR9Growth
