import DiophantineConsistency.CompactConcreteIncrement
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowEven
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem low_even : (CompactConcreteIncrement.mask : V) % 2 = 0 := by
  let M : V := CompactConcreteIncrement.mask
  have ho : M % Exp.exp (67:V) = Exp.exp (67:V)-2 := by
    simpa only [M, CompactConcreteIncrement.mask, dig_zero_index] using (CompactConcreteMask.model_origin (V:=V))
  have hm := mod_mod_of_le (1:V) M 1 67 (by norm_num)
  simp only [one_mul, exp_one] at hm
  have he : Exp.exp (67:V) = 2 * Exp.exp (66:V) := by
    simpa only [show (67:V)=66+1 by norm_num] using (exp_succ (66:V))
  have hr : (Exp.exp (67:V)-2)%2=0 := by
    rw [he, show (2:V)*Exp.exp 66-2 = 2*(Exp.exp 66-1) by rw [mul_tsub, mul_one]]
    simp
  rw [ho, hr] at hm
  exact hm.symm
end CompactLowEven
#print axioms CompactLowEven.low_even
