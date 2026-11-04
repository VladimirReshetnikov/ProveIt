import Trace74UniformHeightContradiction
import Mathlib.Tactic.LinearCombination

/-! Uniform quotient obstruction for the reduced graph projection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74UniformBoundedQuotient
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

private theorem eq_zero_of_small_dvd (d z : R)
    (hdisc : ∀ t : R, 0<t → 1≤t)
    (hdpos : 0<d) (hlo : -d<z) (hhi : z<d) (hd : d∣z) : z=0 := by
  obtain ⟨t,ht⟩ := hd
  rcases lt_trichotomy t 0 with hn | hz | hp
  · have hneg : 1≤ -t := hdisc (-t) (neg_pos.mpr hn)
    have hm := mul_le_mul_of_nonneg_left hneg (le_of_lt hdpos)
    nlinarith [ht]
  · simp only [hz,mul_zero] at ht
    exact ht
  · have hpos : 1≤t := hdisc t hp
    have hm := mul_le_mul_of_nonneg_left hpos (le_of_lt hdpos)
    nlinarith [ht]

/-- An explicitly bounded quotient contradicts the variable-parameter
reduced projection in a discretely ordered ring. -/
theorem impossible_of_bounded_quotient (h x y L j : R)
    (hdisc : ∀ t : R, 0<t → 1≤t)
    (hh : 0<h) (hy : 0<y) (hL : 0<L)
    (hjpos : 0<j) (hjlt : j<y) (hLh : L*h<y)
    (heq : h*(4*y-1)*(4*(4*L+1)*y-1)*((4*L-1)*y-L) =
      (4*y*(x+1)-1)*j) : False := by
  have hLhpos : 0<L*h := mul_pos hL hh
  have hmod : y ∣ j-L*h := by
    refine ⟨4*(x+1)*j-h*((256*L^2-16)*y^2+(-128*L^2-32*L+8)*y+(16*L^2+12*L-1)), ?_⟩
    linear_combination heq
  have hzero : j-L*h=0 := eq_zero_of_small_dvd y (j-L*h) hdisc hy
    (by linarith) (by linarith) hmod
  have hj : j=L*h := by linarith
  have hprod : (4*y-1)*(4*(4*L+1)*y-1)*((4*L-1)*y-L)=L*(4*y*(x+1)-1) := by
    apply mul_left_cancel₀ (ne_of_gt hh)
    calc
      h*((4*y-1)*(4*(4*L+1)*y-1)*((4*L-1)*y-L)) =
          (4*y*(x+1)-1)*j := by simpa only [mul_assoc] using heq
      _ = h*(L*(4*y*(x+1)-1)) := by rw [hj]; ring
  have hdiv : (4*y) ∣ y := by
    refine ⟨((64*L^2-4)*y^2+(-32*L^2-8*L+2)*y+(4*L^2+3*L))-L*(x+1), ?_⟩
    linear_combination -hprod
  have hz : y=0 := eq_zero_of_small_dvd (4*y) y hdisc
    (by positivity) (by linarith) (by linarith) hdiv
  linarith

#print axioms Trace74UniformBoundedQuotient.impossible_of_bounded_quotient
end Trace74UniformBoundedQuotient
