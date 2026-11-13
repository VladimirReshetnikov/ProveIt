import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Unchecked source draft. Conditional ordered-ring estimates only. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4R5ScalarGrowth
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem quartic_bound (x : R) (hx : 32 ≤ x) : (x+2)^4 ≤ 2*x^4 := by
  have hu : 0 ≤ x-32 := sub_nonneg.mpr hx
  have hp : 0 ≤ 760816+104928*(x-32)+5352*(x-32)^2+
      120*(x-32)^3+(x-32)^4 := by positivity
  have hi : 2*x^4-(x+2)^4 = 760816+104928*(x-32)+5352*(x-32)^2+
      120*(x-32)^3+(x-32)^4 := by ring
  linarith

theorem x_gt_four_y_cube (x y : R) (hx : 32 ≤ x) (hy : 1 ≤ y)
    (hgap : (128*(x*y^2)^3+192*(x*y^2)^2+80*(x*y^2)+8)*y <
      16*(y*(x+1)+1)^4-12*(y*(x+1)+1)^2+1) :
    4*y^3 < x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hP : 0 ≤ x*y^2 := by positivity
  have hlower : 128*x^3*y^7 ≤
      (128*(x*y^2)^3+192*(x*y^2)^2+80*(x*y^2)+8)*y := by
    have hh : 0 ≤ (192*(x*y^2)^2+80*(x*y^2)+8)*y := by positivity
    nlinarith [hh]
  let t := y*(x+1)+1
  have ht : 1 ≤ t := by dsimp [t]; nlinarith
  have ht0 : 0 ≤ t := by linarith
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hupper : 16*t^4-12*t^2+1 ≤ 16*t^4 := by nlinarith
  have htbound : t ≤ y*(x+2) := by dsimp [t]; nlinarith
  have hpow : t^4 ≤ (y*(x+2))^4 := pow_le_pow_left₀ ht0 htbound 4
  have hquartic := quartic_bound x hx
  have hy4 : 0 ≤ y^4 := by positivity
  have hm := mul_le_mul_of_nonneg_left hquartic hy4
  have hproduct : (y*(x+2))^4 ≤ 2*x^4*y^4 := by nlinarith [hm]
  have hg : 128*x^3*y^7 < 32*x^4*y^4 := by
    dsimp [t] at hupper hpow
    nlinarith [hlower, hupper, hpow, hproduct]
  have hf : 0 < 32*x^3*y^4 := by positivity
  have hmul : (32*x^3*y^4)*(4*y^3) < (32*x^3*y^4)*x := by
    nlinarith [hg]
  exact (mul_lt_mul_left hf).mp hmul

theorem h_large (q x y : R) (hq : 32 ≤ q) (hy : q^3 ≤ y)
    (hx : 4*y^3 < x) : 16368*q*y^3 < 4*y*(x+1)-1 := by
  have hq0 : 0 < q := by linarith
  have hq2 : 1024 ≤ q^2 := by nlinarith [sq_nonneg (q-32)]
  have hqcube := mul_le_mul_of_nonneg_right hq2 (le_of_lt hq0)
  have hy1 : 1 ≤ y := by nlinarith [hqcube]
  have hy0 : 0 < y := by linarith
  have hq3 : 16368*q < 16*q^3 := by
    have hm := mul_le_mul_of_nonneg_right hq2 (le_of_lt hq0)
    nlinarith [hm]
  have hc : 16368*q < 16*y := by nlinarith
  have hp : 0 < y^3 := by positivity
  have hm := mul_lt_mul_of_pos_right hc hp
  have hxmul := mul_lt_mul_of_pos_left hx hy0
  nlinarith [hm, hxmul]

#print axioms Trace74N4R5ScalarGrowth.quartic_bound
#print axioms Trace74N4R5ScalarGrowth.x_gt_four_y_cube
#print axioms Trace74N4R5ScalarGrowth.h_large
end Trace74N4R5ScalarGrowth
