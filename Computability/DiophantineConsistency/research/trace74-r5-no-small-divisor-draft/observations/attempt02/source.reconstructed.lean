import Trace74N4R5ScalarGrowth

/-! UNCHECKED DRAFT. The reduced r=5 divisor is too small in a discrete
ordered ring under the stated scalar size assumptions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74R5NoSmallDivisor
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem impossible (q x y : R)
    (hdisc : ∀ z : R, 0<z → 1≤z)
    (hq : 32≤q) (hy : q^3≤y) (hx : 4*y^3<x)
    (hd : (4*y*(x+1)-1) ∣ (q-1)*(4*y-1)*(132*y-1)*(31*y-8)) : False := by
  have hq0 : 0<q := by linarith
  have hq1 : 1<q := by linarith
  have hqone : 1≤q := le_of_lt hq1
  have hq2 : 1≤q*q := by nlinarith
  have hqcube : 1≤q^3 := by
    have hh := mul_le_mul_of_nonneg_left hqone (sq_nonneg q)
    have hh' : q*q≤q^3 := by simpa only [pow_succ,pow_two,mul_one] using hh
    exact le_trans hq2 hh'
  have hy1 : 1≤y := le_trans hqcube hy
  have hy0 : 0<y := lt_of_lt_of_le (by norm_num : (0:R)<1) hy1
  have hh : 0<q-1 := sub_pos.mpr hq1
  have ha : 0<4*y-1 := by linarith
  have hb : 0<132*y-1 := by linarith
  have hc : 0<31*y-8 := by linarith
  have hprod : 0<(q-1)*(4*y-1)*(132*y-1)*(31*y-8) := by positivity
  have hprod_bound : (q-1)*(4*y-1)*(132*y-1)*(31*y-8)<16368*q*y^3 := by
    have h1 : q-1<q := by linarith
    have h2 : 4*y-1<4*y := by linarith
    have h3 : 132*y-1<132*y := by linarith
    have h4 : 31*y-8<31*y := by linarith
    have hh1 : (q-1)*(4*y-1)<q*(4*y) := mul_lt_mul h1 (le_of_lt h2) (le_of_lt ha) (le_of_lt hq0)
    have hh2 : (q-1)*(4*y-1)*(132*y-1)<q*(4*y)*(132*y) :=
      mul_lt_mul hh1 (le_of_lt h3) (le_of_lt hb) (by positivity)
    have hh3 : (q-1)*(4*y-1)*(132*y-1)*(31*y-8)<q*(4*y)*(132*y)*(31*y) :=
      mul_lt_mul hh2 (le_of_lt h4) (le_of_lt hc) (by positivity)
    convert hh3 using 1; ring
  have hlarge := Trace74N4R5ScalarGrowth.h_large q x y hq hy hx
  have hH : 0<4*y*(x+1)-1 := lt_trans hprod (lt_trans hprod_bound hlarge)
  obtain ⟨z,hz⟩ := hd
  have hzpos : 0<z := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hH) (le_of_not_gt hn)
    rw [←hz] at hh
    exact (not_le_of_gt hprod) hh
  have hle : 4*y*(x+1)-1≤(q-1)*(4*y-1)*(132*y-1)*(31*y-8) := by
    rw [hz]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hdisc z hzpos) (le_of_lt hH)
  exact (not_le_of_gt (lt_trans hprod_bound hlarge)) hle

#print axioms Trace74R5NoSmallDivisor.impossible
end Trace74R5NoSmallDivisor
