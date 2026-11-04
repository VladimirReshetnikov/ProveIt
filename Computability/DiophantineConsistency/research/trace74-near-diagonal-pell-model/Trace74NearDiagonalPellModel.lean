import DiophantineConsistency.ArithmeticHalfBinomialSandwich
import DiophantineConsistency.ModelDifferenceRing

/-! Model-safe power bounds for the near-diagonal strict Pell gap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74NearDiagonalPellModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open ArithmeticPow ArithmeticHalfBinomialSandwich
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The strict ordinate gap implies the power gap at arbitrary model indices.
    Both exponentiation and the induction in the two sandwich lemmas are internal. -/
theorem strict_power_gap (t l u a b n r : V)
    (hl : l≤2*b+3) (hu : 2*(a+2)≤u)
    (hgap : t*ycoord (n+1) b<ycoord (r+1) a) :
    t*power l n<power u r := by
  have hlo : power l n≤ycoord (n+1) b :=
    le_trans (power_mono_base l (2*b+3) n hl) (power_le_ycoord b n)
  have hhi : ycoord (r+1) a≤power u r :=
    le_trans (ycoord_le_power a r) (power_mono_base (2*(a+2)) u r hu)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlo (by simp)) (lt_of_lt_of_le hgap hhi)

/-- Instantiation of the two Pell bases used by the 74-operation candidate.
    The strict-gap premise and the values X,Y are still explicit assumptions. -/
theorem trace74_strict_power_gap (X Y n r : V) (hX : 2≤X) (hY : 1≤Y)
    (hgap : (2*Y)*ycoord (n+1) (2*(X*Y*Y-1)+1)<
      ycoord (r+1) (Y*(X+1)-1)) :
    (2*Y)*power (X*(2*Y)*(2*Y)) n<power (2*X*(2*Y)) r := by
  have hXY : 1≤X*Y*Y := one_le_mul (one_le_mul (le_trans (by norm_num) hX) hY) hY
  have hA : 1≤Y*(X+1) := one_le_mul hY (by simp)
  have hP : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le hXY
  have hQ : Y*(X+1)-1+1=Y*(X+1) := tsub_add_cancel_of_le hA
  have hlo : X*(2*Y)*(2*Y)≤2*(2*(X*Y*Y-1)+1)+3 := by
    have hid : 2*(2*(X*Y*Y-1)+1)+3=4*(X*Y*Y-1+1)+1 := by ring
    rw [hid,hP]
    have : X*(2*Y)*(2*Y)=4*(X*Y*Y) := by ring
    rw [this]
    simp
  have hhi : 2*((Y*(X+1)-1)+2)≤2*X*(2*Y) := by
    have hid : 2*((Y*(X+1)-1)+2)=2*(Y*(X+1)-1+1)+2 := by ring
    rw [hid,hQ]
    apply ι_le_ι.mp
    simp only [map_add,map_mul,map_one,map_ofNat]
    have hx : (2:DiffRing V)≤ι X := by simpa only [map_ofNat] using (ι_le_ι.mpr hX)
    have hy : (1:DiffRing V)≤ι Y := by simpa only [map_one] using (ι_le_ι.mpr hY)
    have hproduct := mul_nonneg (show (0:DiffRing V)≤ι Y-1 by linarith)
      (show (0:DiffRing V)≤ι X-2 by linarith)
    nlinarith
  exact strict_power_gap (2*Y) (X*(2*Y)*(2*Y)) (2*X*(2*Y))
    (Y*(X+1)-1) (2*(X*Y*Y-1)+1) n r hlo hhi hgap

#print axioms Trace74NearDiagonalPellModel.strict_power_gap
#print axioms Trace74NearDiagonalPellModel.trace74_strict_power_gap
end Trace74NearDiagonalPellModel
