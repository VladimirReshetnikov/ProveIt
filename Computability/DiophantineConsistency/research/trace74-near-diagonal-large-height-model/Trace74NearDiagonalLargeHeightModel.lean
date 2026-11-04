import Trace74NearDiagonalHeightModel

/-! Model-safe cancellation from the two height-power inequalities. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74NearDiagonalLargeHeightModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPellRecurrence
open Trace74NearDiagonalPellModel Trace74NearDiagonalHeightModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem power_four' (x : V) : power x 4=x*x*x*x := by
  have h : (4:V)=(2:V)+2 := by norm_num
  have h2 : (2:V)=1+1 := by norm_num
  rw [h,power_add,h2,power_succ,power_one]
  ring

/-- The ordinary near-diagonal height amplification, uniformly over model
indices, assuming the lower power estimate explicitly. -/
theorem amplified_height (X Y h K k : V) (hY : 1≤Y)
    (hsmall : power Y (k+4)<8*X*X)
    (hlarge : 512*h*h*K*K*K*K<power Y k) :
    8*h*K*K*Y*Y<X := by
  have hy4 : 0<Y*Y*Y*Y := by
    have : 0<Y := lt_of_lt_of_le (by norm_num) hY
    positivity
  have hgrow := mul_lt_mul_of_pos_right hlarge hy4
  have hy : power Y (k+4)=power Y k*(Y*Y*Y*Y) := by
    rw [power_add,power_four']
  have hsq8 : 8*((8*h*K*K*Y*Y)*(8*h*K*K*Y*Y))<8*(X*X) := calc
    _=(512*h*h*K*K*K*K)*(Y*Y*Y*Y) := by ring
    _<power Y k*(Y*Y*Y*Y) := hgrow
    _=power Y (k+4) := hy.symm
    _<8*(X*X) := by simpa only [mul_assoc] using hsmall
  have hsq : (8*h*K*K*Y*Y)*(8*h*K*K*Y*Y)<X*X :=
    (mul_lt_mul_iff_of_pos_left (by norm_num : (0:V)<8)).mp hsq8
  by_contra hn
  have hle : X≤8*h*K*K*Y*Y := le_of_not_gt hn
  have hsle : X*X≤(8*h*K*K*Y*Y)*(8*h*K*K*Y*Y) :=
    mul_le_mul hle hle (by simp) (by simp)
  exact (not_lt_of_ge hsle) hsq

#print axioms Trace74NearDiagonalLargeHeightModel.amplified_height
end Trace74NearDiagonalLargeHeightModel
