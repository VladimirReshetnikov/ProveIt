import Trace74Width3PellHeightModel
import Trace74PellGapBinding
import Trace74R13Height

/-! Same-tuple height for first index 10 and main index 13. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N10R13ModelHeight
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74PellGapBinding Trace74Width3PellHeightModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem power_seven (x : V) : power x 7=x^7 := by
  rw [show (7:V)=6+1 by norm_num,power_succ,
    show (6:V)=5+1 by norm_num,power_succ,
    show (5:V)=4+1 by norm_num,power_succ,
    show (4:V)=3+1 by norm_num,power_succ,
    show (3:V)=2+1 by norm_num,power_succ,
    show (2:V)=1+1 by norm_num,power_succ,power_one]
  ring

/-- The two same-tuple ordinates imply the explicit height bound, without
assuming a graph zero. -/
theorem tuple_height (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hq : (1073741824:V)≤q p v)
    (hn : 2*ycoord 10 (2*(firstParam p v-1)+1)=k v)
    (hr : c p v=ycoord 13 (A p v-1)) :
    (536870912:DiffRing V)*ι (b p v)*ι (Y p v)<ι (X p v) := by
  have hqpos : 0<q p v := lt_of_lt_of_le (by norm_num) hq
  have hY : 1≤Y p v := pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos hqpos hqpos) hqpos) (hv 6))
  have hX : (2:V)≤X p v := calc
    (2:V)≤q p v := le_trans (by norm_num) hq
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (pos_iff_one_le.mp (hv 5)) (show (0:V)≤q p v by simp)
    _=X p v := rfl
  have hgap := tuple_pell_gap p v (10:V) (13:V) (hv 8) hn hr
  have hgap' : (2*Y p v)*ycoord (((6:V)+3)+1) (2*(X p v*Y p v*Y p v-1)+1)<
      ycoord ((12:V)+1) (Y p v*(X p v+1)-1) := by
    simpa only [show ((6:V)+3)+1=10 by norm_num,show (12:V)+1=13 by norm_num] using hgap
  have hsmall := pell_gap_height (X p v) (Y p v) (6:V) (12:V) hX hY (by norm_num) hgap'
  have hsmall' : (Y p v)^7<32*(X p v)^3 := by
    simpa only [show (6:V)+1=7 by norm_num,power_seven,pow_succ,pow_zero,one_mul,mul_one,mul_assoc] using hsmall
  have hYq : (q p v)^3≤Y p v := by
    have hh := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (show (0:V)≤(q p v)^3 by simp)
    simpa only [mul_one,Y,pow_succ,pow_zero,one_mul,mul_assoc] using hh
  have hh : 0<b p v := mul_pos hb (hv 0)
  have hhq : b p v<q p v := by change b p v<b p v+1; exact lt_add_of_pos_right _ (by norm_num)
  apply Trace74R13Height.height (ι (q p v)) (ι (b p v)) (ι (X p v)) (ι (Y p v))
  · simpa only [map_ofNat] using (ι_le_ι.mpr hq)
  · simpa only [map_zero] using (ι_lt_ι.mpr hh)
  · exact ι_lt_ι.mpr hhq
  · simpa only [map_pow] using (ι_le_ι.mpr hYq)
  · exact ι_nonneg _
  · simpa only [map_pow,map_mul,map_ofNat] using (ι_lt_ι.mpr hsmall')

#print axioms Trace74N10R13ModelHeight.tuple_height
end Trace74N10R13ModelHeight
