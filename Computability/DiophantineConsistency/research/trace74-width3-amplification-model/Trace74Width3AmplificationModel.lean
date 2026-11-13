import Trace74NearDiagonalLargeHeightModel

/-! Width-three model-power amplification; the two power bounds are explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74Width3AmplificationModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem power_six' (x : V) : power x 6=x*x*x*x*x*x := by
  have h2 : power x 2=x*x := by
    rw [show (2:V)=1+1 by norm_num,power_succ,power_one]
  have h4 : power x 4=x*x*x*x := by
    rw [show (4:V)=2+2 by norm_num,power_add,h2]
    ring
  rw [show (6:V)=4+2 by norm_num,power_add,h4,h2]
  ring

/-- Width three: a strict lower and upper power bound force the height gap. -/
theorem amplified_height (X Y h K k : V) (hY : 1≤Y)
    (hsmall : power Y (k+6)<32*X*X*X)
    (hlarge : 16384*h*h*h*K*K*K*K*K*K<power Y k) :
    8*h*K*K*Y*Y<X := by
  have hy6 : 0<Y*Y*Y*Y*Y*Y := by
    have : 0<Y := lt_of_lt_of_le (by norm_num) hY
    positivity
  have hgrow := mul_lt_mul_of_pos_right hlarge hy6
  have hy : power Y (k+6)=power Y k*(Y*Y*Y*Y*Y*Y) := by
    rw [power_add,power_six']
  let W := 8*h*K*K*Y*Y
  have hcube32 : 32*(W*W*W)<32*(X*X*X) := calc
    _=(16384*h*h*h*K*K*K*K*K*K)*(Y*Y*Y*Y*Y*Y) := by dsimp [W]; ring
    _<power Y k*(Y*Y*Y*Y*Y*Y) := hgrow
    _=power Y (k+6) := hy.symm
    _<32*(X*X*X) := by simpa only [mul_assoc] using hsmall
  have hcube : W*W*W<X*X*X :=
    (mul_lt_mul_iff_of_pos_left (by norm_num : (0:V)<32)).mp hcube32
  by_contra hn
  have hle : X≤W := le_of_not_gt hn
  have hsq : X*X≤W*W := mul_le_mul hle hle (by simp) (by simp)
  have hcub : X*X*X≤W*W*W := mul_le_mul hsq hle (by simp) (by simp)
  exact (not_lt_of_ge hcub) hcube

#print axioms Trace74Width3AmplificationModel.amplified_height
end Trace74Width3AmplificationModel
