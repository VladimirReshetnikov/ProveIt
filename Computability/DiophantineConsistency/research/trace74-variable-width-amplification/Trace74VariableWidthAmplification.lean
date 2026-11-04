import Trace74VariableWidthSizeModel

/-! Variable-width model height amplification. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74VariableWidthAmplification
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A strict Pell power upper bound and a nonstrict size lower bound force
the height gap, for an arbitrary internal width `c`. -/
theorem amplified_height (X Y h K m c : V)
    (hsmall : 2*power Y (m+2*c+1)<power 2 (2*c)*power X c)
    (hlarge : power 2 (5*c)*power h c*power K (2*c)≤power Y (m+1)) :
    8*h*K*K*Y*Y<X := by
  let W : V := 8*h*K*K*Y*Y
  have h2pos : 0<power (2:V) (2*c) := power_pos 2 (2*c) (by norm_num)
  have h8 : power (8:V) c=power 2 (3*c) := by
    have hp : power (2:V) 3=8 := by
      rw [show (3:V)=1+1+1 by norm_num,power_succ,power_succ,power_one]
      norm_num
    rw [←hp,power_iterate]
  have hK : power K (2*c)=power K c*power K c := by
    rw [show 2*c=c+c by ring,power_add]
  have hY : power Y (2*c)=power Y c*power Y c := by
    rw [show 2*c=c+c by ring,power_add]
  have hW : power W c=
      power 2 (3*c)*power h c*power K (2*c)*power Y (2*c) := by
    dsimp [W]
    simp only [power_mul_base,h8,hK,hY]
    ring
  have h2 : power (2:V) (2*c)*power 2 (3*c)=power 2 (5*c) := by
    rw [←power_add,show 2*c+3*c=5*c by ring]
  have hy : power Y (m+2*c+1)=power Y (m+1)*power Y (2*c) := by
    rw [show m+2*c+1=(m+1)+2*c by ring,power_add]
  have hfactor : power 2 (2*c)*(2*power W c)<power 2 (2*c)*power X c := calc
    _=2*(power 2 (5*c)*power h c*power K (2*c))*power Y (2*c) := by
      rw [hW,←h2]
      ring
    _≤2*(power Y (m+1)*power Y (2*c)) := by
      have hm := mul_le_mul_of_nonneg_right hlarge (show (0:V)≤power Y (2*c) by simp)
      have hm2 := mul_le_mul_of_nonneg_left hm (show (0:V)≤2 by simp)
      simpa only [mul_assoc] using hm2
    _=2*power Y (m+2*c+1) := by rw [hy]
    _<power 2 (2*c)*power X c := hsmall
  have hc := (mul_lt_mul_iff_of_pos_left h2pos).mp hfactor
  have hc' : power W c<power X c := by
    have hle : power W c≤2*power W c := by simp
    exact lt_of_le_of_lt hle hc
  by_contra hn
  have hle : X≤W := le_of_not_gt hn
  exact (not_lt_of_ge (power_mono_base X W c hle)) hc'

#print axioms Trace74VariableWidthAmplification.amplified_height
end Trace74VariableWidthAmplification
