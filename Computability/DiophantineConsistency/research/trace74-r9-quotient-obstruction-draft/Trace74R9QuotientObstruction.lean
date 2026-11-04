import Trace74R5NoSmallDivisor
import Mathlib.Tactic.LinearCombination

/-! UNCHECKED DRAFT: bounded quotient obstruction for the r=9 projection.
All size hypotheses are explicit; no graph or Pell hypothesis is inferred. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74R9QuotientObstruction
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem eq_zero_of_small_dvd (d z : R)
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

theorem impossible_of_bounded_quotient (h x y j : R)
    (hdisc : ∀ t : R, 0<t → 1≤t)
    (hh : 0<h) (hy : 0<y)
    (hjpos : 0<j) (hjlt : j<y) (h128lt : 128*h<y)
    (heq : h*(4*y-1)*(2052*y-1)*(511*y-128) =
      (4*y*(x+1)-1)*j) : False := by
  have hmod : y ∣ j-128*h := by
    refine ⟨4*(x+1)*j-h*(4194288*y^2-2101240*y+263679), ?_⟩
    linear_combination heq
  have hzero : j-128*h=0 := eq_zero_of_small_dvd y (j-128*h) hdisc hy
    (by linarith) (by linarith) hmod
  have hj : j=128*h := by linarith
  have hprod : (4*y-1)*(2052*y-1)*(511*y-128)=128*(4*y*(x+1)-1) := by
    apply mul_left_cancel₀ (ne_of_gt hh)
    calc
      h*((4*y-1)*(2052*y-1)*(511*y-128)) =
          (4*y*(x+1)-1)*j := by simpa only [mul_assoc] using heq
      _ = h*(128*(4*y*(x+1)-1)) := by rw [hj]; ring
  have hdiv : (4*y) ∣ (3*y) := by
    refine ⟨128*x-1048572*y^2+525310*y-65791, ?_⟩
    linear_combination hprod
  have hz : 3*y=0 := eq_zero_of_small_dvd (4*y) (3*y) hdisc
    (by positivity) (by linarith) (by linarith) hdiv
  linarith

#print axioms Trace74R9QuotientObstruction.eq_zero_of_small_dvd
#print axioms Trace74R9QuotientObstruction.impossible_of_bounded_quotient
end Trace74R9QuotientObstruction
