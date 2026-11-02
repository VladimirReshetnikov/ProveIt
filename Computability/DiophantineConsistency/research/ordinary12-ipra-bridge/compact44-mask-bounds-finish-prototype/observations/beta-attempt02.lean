import DiophantineConsistency.CompactSymbolicGraphDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactBetaResidues
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem residues (β : V) (hβ : β+1=Exp.exp ((67:V)*8807)) : β%2=1 ∧ β%8=7 := by
  let E : V := Exp.exp (590066:V)
  have hE : Exp.exp ((67:V)*8807)=8*E := by
    change Exp.exp ((67:V)*8807)=8*Exp.exp (590066:V)
    rw [show ((67:V)*8807)=590066+1+1+1 by norm_num, exp_succ,exp_succ,exp_succ]
    ring
  have hE1 : E-1+1=E := tsub_add_cancel_of_le (pos_iff_one_le.mp (by dsimp [E]; exact exp_pos _))
  have hform : β=8*(E-1)+7 := by
    have heq : β+1=(8*(E-1)+7)+1 := by
      calc β+1=8*E := by rw [hβ,hE]
        _=(8*(E-1)+7)+1 := by rw [←hE1]; ring
    exact add_right_cancel heq
  constructor
  · rw [hform, show (8*(E-1)+7:V)=2*(4*(E-1)+3)+1 by ring,
      mod_mul_add' _ _ (by norm_num : (0:V)<2)]
    exact mod_eq_self_of_lt (by norm_num)
  · rw [hform, mod_mul_add' _ _ (by norm_num : (0:V)<8)]
    exact mod_eq_self_of_lt (by norm_num)
end CompactBetaResidues
#print axioms CompactBetaResidues.residues
