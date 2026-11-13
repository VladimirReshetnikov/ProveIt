import DiophantineConsistency.Mixed121.W121.TemporalShiftSplit
/-! Width-121 port of `Compact44/TemporalCleanNumerics` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalCleanNumerics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem boolean_high_zero (r x : V) (hr : r<121) (hx : x≤1) :
    x / Exp.exp (121-r)=0 := by
  have hpos : 0<121-r := tsub_pos_iff_lt.mpr hr
  have hE : (2:V)≤Exp.exp (121-r) := by
    have h := exp_monotone_le.mpr (pos_iff_one_le.mp hpos)
    simpa only [exp_one] using h
  have hlt : x<Exp.exp (121-r) := lt_of_le_of_lt hx (lt_of_lt_of_le (by norm_num) hE)
  exact div_eq_zero_of_lt _ hlt

theorem boolean_low_bound (r x : V) (hr : r<121) (hx : x≤1) :
    (x*Exp.exp r)%Exp.exp 121 ≤ Exp.exp 120 := by
  have hr66 : r≤120 := by
    apply (add_le_add_iff_right (1:V)).mp
    simpa only [show (120:V)+1=121 by norm_num] using lt_iff_succ_le.mp hr
  have hbound : Exp.exp r≤Exp.exp 120 := exp_monotone_le.mpr hr66
  rcases lt_or_eq_of_le hx with hlt | heq
  · have hz : x=0 := lt_one_iff_eq_zero.mp hlt
    rw [hz,zero_mul,zero_mod]
    exact Arithmetic.zero_le _
  · rw [heq,one_mul]
    exact le_trans (mod_le _ _) hbound

theorem clean_of_formulas (r x y target predecessor : V)
    (hr : r<121) (hx : x≤1) (hy : y≤1)
    (htarget : target=(0*Exp.exp r)%Exp.exp 121 + x/Exp.exp (121-r))
    (hpred : predecessor=(x*Exp.exp r)%Exp.exp 121 + y/Exp.exp (121-r)) :
    target=0 ∧ predecessor≤Exp.exp 120 := by
  have hx0 := boolean_high_zero r x hr hx
  have hy0 := boolean_high_zero r y hr hy
  constructor
  · rw [htarget,hx0]
    simp
  · rw [hpred,hy0,add_zero]
    exact boolean_low_bound r x hr hx
#print axioms W121.TemporalCleanNumerics.boolean_high_zero
#print axioms W121.TemporalCleanNumerics.boolean_low_bound
#print axioms W121.TemporalCleanNumerics.clean_of_formulas
end W121.TemporalCleanNumerics
