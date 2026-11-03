import DiophantineConsistency.CompactConcreteIncrement
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowModFour
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The compact symbolic low mask has residue two modulo four in every model. -/
theorem low_mod_four : (CompactConcreteIncrement.mask : V) % 4 = 2 := by
  let M : V := CompactConcreteIncrement.mask
  have ho : M % Exp.exp (67:V) = Exp.exp (67:V)-2 := by
    simpa only [M, CompactConcreteIncrement.mask, dig_zero_index] using (CompactConcreteMask.model_origin (V:=V))
  have hp : Exp.exp (65:V)-1+1=Exp.exp 65 := tsub_add_cancel_of_le (one_le_exp _)
  have hE : Exp.exp (67:V)=4*(Exp.exp 65-1)+4 := calc
    _=2*(2*Exp.exp (65:V)) := by
      rw [show (67:V)=(65:V)+1+1 by norm_num,exp_succ,exp_succ]
    _=4*(Exp.exp 65-1)+4 := by
      conv_lhs => rw [←hp]
      ring
  have hr : (Exp.exp (67:V)-2)%4=2 := by
    rw [hE, show (4:V)*(Exp.exp 65-1)+4 = (4*(Exp.exp 65-1)+2)+2 by ring,
      add_tsub_cancel_right,
      add_comm, mod_add_mul' _ _ (by norm_num), mod_eq_self_of_lt (by norm_num : (2:V)<4)]
  have he2 : Exp.exp (2:V) = 4 := by
    rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
    norm_num
  have hm := mod_mod_of_le (1:V) M 2 67 (by norm_num)
  simp only [one_mul, he2] at hm
  rw [ho, hr] at hm
  exact hm.symm
end CompactLowModFour
#print axioms CompactLowModFour.low_mod_four
