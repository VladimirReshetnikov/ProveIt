import Trace74PellGapBinding

/-! The upper half of the positive same-tuple Pell interval. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74UpperPellGapModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPow ArithmeticHalfBinomialSandwich
open Trace75Factors Trace74Pell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positive second offset puts the main ordinate strictly below
`k*(Y+1)`, complementing the lower inequality from the first offset. -/
theorem tuple_upper_pell_gap (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hv9 : 0<v 9)
    (hn : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hr : c p v=ycoord r (A p v-1)) :
    ycoord r (Y p v*(X p v+1)-1) <
      (2*(Y p v+1))*ycoord n (2*(X p v*Y p v*Y p v-1)+1) := by
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hP : firstParam p v=X p v*Y p v*Y p v := by dsimp [firstParam]; ring
  have hv : v 8<k v := by
    change v 8<v 8+v 9
    exact lt_add_of_pos_right _ hv9
  have hlt : c p v<k v*(Y p v+1) := by
    change k v*Y p v+v 8<k v*(Y p v+1)
    calc
      _<k v*Y p v+k v := add_lt_add_right hv _
      _=k v*(Y p v+1) := by ring
  rw [←hn,hr,hA,hP] at hlt
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hlt

/-- The upper Pell interval yields a reverse represented-power inequality
at positive internal indices. -/
theorem tuple_upper_power_gap (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hX : 1≤X p v) (hY : 1≤Y p v) (hn1 : 1≤n) (hr1 : 1≤r)
    (hv9 : 0<v 9)
    (hn : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hr : c p v=ycoord r (A p v-1)) :
    power (2*Y p v*(X p v+1)) (r-1) <
      (2*(Y p v+1))*power (X p v*(2*Y p v)*(2*Y p v)+2) (n-1) := by
  let X0 := X p v
  let Y0 := Y p v
  let j := n-1
  let s := r-1
  have hn' : j+1=n := tsub_add_cancel_of_le hn1
  have hr' : s+1=r := tsub_add_cancel_of_le hr1
  have hXY : 1≤X0*Y0*Y0 := one_le_mul (one_le_mul hX hY) hY
  have hA : 1≤Y0*(X0+1) := one_le_mul hY (by simp)
  have hP : X0*Y0*Y0-1+1=X0*Y0*Y0 := tsub_add_cancel_of_le hXY
  have hQ : Y0*(X0+1)-1+1=Y0*(X0+1) := tsub_add_cancel_of_le hA
  have hl : 2*Y0*(X0+1)≤2*(Y0*(X0+1)-1)+3 := by
    have hid : 2*(Y0*(X0+1)-1)+3=2*(Y0*(X0+1)-1+1)+1 := by ring
    rw [hid,hQ]
    have he : 2*Y0*(X0+1)=2*(Y0*(X0+1)) := by ring
    rw [he]
    simp
  have hu : 2*(2*(X0*Y0*Y0-1)+1+2)=X0*(2*Y0)*(2*Y0)+2 := by
    have hid : 2*(2*(X0*Y0*Y0-1)+1+2)=4*(X0*Y0*Y0-1+1)+2 := by ring
    rw [hid,hP]
    ring
  have hlo : power (2*Y0*(X0+1)) s≤ycoord (s+1) (Y0*(X0+1)-1) :=
    le_trans (power_mono_base _ _ s hl) (power_le_ycoord _ s)
  have hhi : ycoord (j+1) (2*(X0*Y0*Y0-1)+1)≤
      power (X0*(2*Y0)*(2*Y0)+2) j := by
    simpa only [hu] using ycoord_le_power (2*(X0*Y0*Y0-1)+1) j
  have hgap := tuple_upper_pell_gap p v n r hv9 hn hr
  change ycoord r (Y0*(X0+1)-1)<(2*(Y0+1))*ycoord n (2*(X0*Y0*Y0-1)+1) at hgap
  rw [←hn',←hr'] at hgap
  exact lt_of_le_of_lt hlo (lt_of_lt_of_le hgap (mul_le_mul_of_nonneg_left hhi (by simp)))

#print axioms Trace74UpperPellGapModel.tuple_upper_pell_gap
#print axioms Trace74UpperPellGapModel.tuple_upper_power_gap
end Trace74UpperPellGapModel
