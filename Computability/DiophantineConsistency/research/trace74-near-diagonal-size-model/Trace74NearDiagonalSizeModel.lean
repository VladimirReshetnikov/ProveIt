import Trace74NearDiagonalLargeHeightModel

/-! Uniform model-power lower bound for the near-diagonal height argument. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74NearDiagonalSizeModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPellRecurrence
open Trace74NearDiagonalPellModel Trace74NearDiagonalHeightModel Trace74NearDiagonalLargeHeightModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem two_pow_ten : power (2:V) 10=1024 := by
  have h2 : power (2:V) 2=4 := by
    rw [show (2:V)=1+1 by norm_num,power_succ,power_one]
    norm_num
  have h4 : power (2:V) 4=16 := by
    rw [show (4:V)=2+2 by norm_num,power_add,h2]
    norm_num
  have h8 : power (2:V) 8=256 := by
    rw [show (8:V)=4+4 by norm_num,power_add,h4]
    norm_num
  rw [show (10:V)=8+2 by norm_num,power_add,h8,h2]
  norm_num

/-- The size hypotheses force the lower power bound needed to amplify the
near-diagonal height estimate. The graph application has `d=n-8`. -/
theorem lower_power_bound (q Y h K d r : V)
    (hq : 1073741824≤q) (hY : q*q≤Y) (hh : h<q)
    (hr : r≤d+10) (hK : K=power 2 r) :
    512*h*h*K*K*K*K<power Y (d+2) := by
  let P := power (2:V) d
  have hp : 0<P := power_pos 2 d (by norm_num)
  have hq1 : 1≤q := le_trans (by norm_num) hq
  have hqp : 0<q := lt_of_lt_of_le (by norm_num) hq1
  have hq2 : 16≤q*q := by
    have h16 : (4:V)≤q := le_trans (by norm_num) hq
    have h := mul_le_mul h16 h16 (by simp : (0:V)≤(4:V)) (by simp : (0:V)≤q)
    norm_num at h
    exact h
  have hy16 : (16:V)≤Y := le_trans hq2 hY
  have hp4 : power (16:V) d=P*P*P*P := by
    dsimp [P]
    rw [show (16:V)=2*2*2*2 by norm_num]
    repeat' rw [power_mul_base]
  have hyP : P*P*P*P≤power Y d := by
    rw [←hp4]
    exact power_mono_base 16 Y d hy16
  have hKle : K≤1024*P := by
    rw [hK]
    calc
      power 2 r≤power 2 (d+10) := power_mono_exponent 2 r (d+10) (by norm_num) hr
      _=1024*P := by rw [power_add,two_pow_ten]; dsimp [P]; ring
  have hKsq : K*K≤(1024*P)*(1024*P) :=
    mul_le_mul hKle hKle (by simp) (by simp)
  have hKfour : K*K*K*K≤(1024*P)*(1024*P)*(1024*P)*(1024*P) := by
    have h := mul_le_mul hKsq hKsq (by simp) (by simp)
    simpa only [mul_assoc] using h
  have hhsq : h*h≤q*q := mul_le_mul hh.le hh.le (by simp) (by simp)
  have hqbig : (562949953421312:V)<q*q := by
    have h := mul_le_mul hq hq (by simp : (0:V)≤(1073741824:V)) (by simp : (0:V)≤q)
    exact lt_of_lt_of_le (by norm_num) h
  have hqSqPos : 0<q*q := mul_pos hqp hqp
  have hYsq : (q*q)*(q*q)≤Y*Y := mul_le_mul hY hY (by simp) (by simp)
  have hcoeff : (562949953421312:V)*(h*h)<Y*Y := calc
    _≤562949953421312*(q*q) := mul_le_mul_of_nonneg_left hhsq (by simp)
    _<(q*q)*(q*q) := mul_lt_mul_of_pos_right hqbig hqSqPos
    _≤Y*Y := hYsq
  have hp4pos : 0<P*P*P*P := by positivity
  calc
    512*h*h*K*K*K*K≤512*(h*h)*((1024*P)*(1024*P)*(1024*P)*(1024*P)) := by
      have h := mul_le_mul_of_nonneg_left hKfour (show (0:V)≤512*(h*h) by simp)
      simpa only [mul_assoc] using h
    _=(562949953421312:V)*(h*h)*(P*P*P*P) := by ring
    _<(Y*Y)*(P*P*P*P) := mul_lt_mul_of_pos_right hcoeff hp4pos
    _≤(Y*Y)*power Y d := mul_le_mul_of_nonneg_left hyP (by simp)
    _=power Y (d+2) := by
      rw [power_add,show (2:V)=1+1 by norm_num,power_succ,power_one]
      ring

#print axioms Trace74NearDiagonalSizeModel.lower_power_bound
end Trace74NearDiagonalSizeModel
