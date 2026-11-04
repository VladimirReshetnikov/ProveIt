import Trace74N6R11CompactBase
import Mathlib.Tactic.Linarith
/-! Unchecked factored scalar upper endpoint; no graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N6R11CompactUpper
open Trace74N6R11CompactBase
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem upper (x t : R) (hx : 32≤x) (ht : 1≤t)
    (hgap : t*((x*t^2+2)^5-4*(x*t^2+2)^3+3*(x*t^2+2)) <
      (t*(x+1)+2)^10-9*(t*(x+1)+2)^8+28*(t*(x+1)+2)^6-
        35*(t*(x+1)+2)^4+15*(t*(x+1)+2)^2-1) :
    t<B x+260 := by
  by_contra hn
  let T : R := B x+260
  let a : R := x+1
  have hx0 : 0≤x := by linarith
  have ha : 0≤a := by dsimp [a]; linarith
  have htT : T≤t := le_of_not_gt hn
  have hB0 : 0≤B x := by dsimp [B]; positivity
  have hT : 1≤T := by dsimp [T]; linarith
  have hbase := Trace74N6R11CompactBase.base (x-32) (sub_nonneg.mpr hx)
  dsimp at hbase
  have hx' : 32+(x-32)=x := by ring
  rw [hx'] at hbase
  change 0<x^5*T-a^10 ∧ 0<(x^5*T-a^10)*T-C a at hbase
  have hx5 : 0≤x^5 := by positivity
  have hDle : x^5*T-a^10≤x^5*t-a^10 :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left htT hx5) _
  have hD0 : 0≤x^5*t-a^10 := le_trans (le_of_lt hbase.1) hDle
  have hm := mul_le_mul hDle htT (by linarith : 0≤T) hD0
  have hp : 0<(x^5*t-a^10)*t-C a := by linarith [hbase.2,hm]
  have ht0 : 0<t := by linarith
  have ht9 : 0<t^9 := by positivity
  have hp' := mul_pos ht9 hp
  have hkey : a^10*t^10+C a*t^9<x^5*t^11 := by
    have hid : t^9*((x^5*t-a^10)*t-C a)=x^5*t^11-(a^10*t^10+C a*t^9) := by ring
    rw [hid] at hp'
    exact sub_pos.mp hp'
  have hpow (j : ℕ) (hj : j≤9) : t^j≤t^9 := pow_le_pow_right₀ ht hj
  have h0 := mul_le_mul_of_nonneg_left (hpow 0 (by norm_num)) (by positivity : (0:R)≤11)
  have h1 := mul_le_mul_of_nonneg_left (hpow 1 (by norm_num)) (by positivity : (0:R)≤220*a)
  have h2 := mul_le_mul_of_nonneg_left (hpow 2 (by norm_num)) (by positivity : (0:R)≤1287*a^2)
  have h3 := mul_le_mul_of_nonneg_left (hpow 3 (by norm_num)) (by positivity : (0:R)≤3432*a^3)
  have h4 := mul_le_mul_of_nonneg_left (hpow 4 (by norm_num)) (by positivity : (0:R)≤5005*a^4)
  have h5 := mul_le_mul_of_nonneg_left (hpow 5 (by norm_num)) (by positivity : (0:R)≤4368*a^5)
  have h6 := mul_le_mul_of_nonneg_left (hpow 6 (by norm_num)) (by positivity : (0:R)≤2380*a^6)
  have h7 := mul_le_mul_of_nonneg_left (hpow 7 (by norm_num)) (by positivity : (0:R)≤816*a^7)
  have h8 := mul_le_mul_of_nonneg_left (hpow 8 (by norm_num)) (by positivity : (0:R)≤171*a^8)
  have h9 := mul_le_mul_of_nonneg_left (hpow 9 (by norm_num)) (by positivity : (0:R)≤20*a^9)
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9
  have hc : (t*a+2)^10-9*(t*a+2)^8+28*(t*a+2)^6-
      35*(t*a+2)^4+15*(t*a+2)^2-1 ≤ a^10*t^10+C a*t^9 := by
    calc
      (t*a+2)^10-9*(t*a+2)^8+28*(t*a+2)^6-35*(t*a+2)^4+15*(t*a+2)^2-1 =
          a^10*t^10+(11*t^0+220*a*t^1+1287*a^2*t^2+3432*a^3*t^3+
            5005*a^4*t^4+4368*a^5*t^5+2380*a^6*t^6+816*a^7*t^7+
            171*a^8*t^8+20*a^9*t^9) := by ring
      _≤a^10*t^10+(11*t^9+220*a*t^9+1287*a^2*t^9+3432*a^3*t^9+
            5005*a^4*t^9+4368*a^5*t^9+2380*a^6*t^9+816*a^7*t^9+
            171*a^8*t^9+20*a^9*t^9) := add_le_add_left hsum _
      _=a^10*t^10+C a*t^9 := by dsimp [C]; ring
  have hlow : x^5*t^11 ≤ t*((x*t^2+2)^5-4*(x*t^2+2)^3+3*(x*t^2+2)) := by
    have hh : 0≤t*(10*(x*t^2)^4+36*(x*t^2)^3+
        56*(x*t^2)^2+35*(x*t^2)+6) := by positivity
    nlinarith [hh]
  dsimp [a] at hc hkey
  exact (not_lt_of_ge (le_trans (le_trans hc (le_of_lt hkey)) hlow)) hgap

#print axioms Trace74N6R11CompactUpper.upper
end Trace74N6R11CompactUpper
