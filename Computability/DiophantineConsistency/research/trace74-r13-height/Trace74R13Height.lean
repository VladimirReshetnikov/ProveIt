import Trace74UniformHeightContradiction

/-! Ordered-ring growth for first index 10 and main index 13. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74R13Height
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The explicit cubic Pell-height estimate implies the weaker height
needed to bound the r=13 projection quotient. -/
theorem height (q h x y : R)
    (hq : 1073741824≤q) (hh : 0<h) (hhq : h<q)
    (hy : q^3≤y) (hx : 0≤x) (hgap : y^7<32*x^3) :
    536870912*h*y<x := by
  have hqpos : 0<q := by linarith
  have hy1 : 1≤y := by nlinarith [sq_nonneg q]
  have hypos : 0<y := by linarith
  have hq2 : (2147483648:R)≤q*q := by nlinarith
  let z : R := 2147483648*h
  have hz : 0<z := by dsimp [z]; positivity
  have hzy : z<y := calc
    z=2147483648*h := rfl
    _<2147483648*q := mul_lt_mul_of_pos_left hhq (by norm_num)
    _≤q*q*q := by nlinarith [mul_le_mul_of_nonneg_right hq2 (le_of_lt hqpos)]
    _≤y := by simpa only [pow_succ,pow_zero,mul_one,one_mul] using hy
  have hzsq : z*z<y*y := mul_lt_mul hzy hzy.le hz (le_of_lt hypos)
  have hzcube : z*z*z<y*y*y := mul_lt_mul hzsq hzy.le (by positivity) (by positivity)
  have hycube : y*y*y≤y*y*y*y := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy1 (show (0:R)≤y*y*y by positivity)
  have hcoeff : (4951760157141521099596496896:R)*h^3<y^4 := by
    have hc : (4951760157141521099596496896:R)*h^3≤z*z*z := by dsimp [z]; nlinarith [sq_nonneg h]
    nlinarith [hc,hzcube,hycube]
  have hy3 : 0<y^3 := by positivity
  have hbig := mul_lt_mul_of_pos_right hcoeff hy3
  by_contra hn
  have hle : x≤536870912*h*y := le_of_not_gt hn
  have hsq : x*x≤(536870912*h*y)*(536870912*h*y) := mul_le_mul hle hle hx (by positivity)
  have hcube : x*x*x≤(536870912*h*y)*(536870912*h*y)*(536870912*h*y) :=
    mul_le_mul hsq hle hx (by positivity)
  have hupper : 32*x^3≤(4951760157141521099596496896:R)*h^3*y^3 := by
    nlinarith [hcube]
  nlinarith [hgap,hbig,hupper]

#print axioms Trace74R13Height.height
end Trace74R13Height
