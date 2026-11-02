import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelectorConverse
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticBinaryCarry
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_mask : NoCarry (0:V) (Exp.exp 51-2) := by
  rw [noCarry_iff]
  intro i
  simp

theorem one_mask : NoCarry (1+Exp.exp (51:V)) (Exp.exp 51-2) := by
  have hE : (1:V)<Exp.exp 51 := by
    have he : (2:V)≤Exp.exp 51 := by
      simpa only [exp_one] using (exp_monotone_le.mpr (by norm_num : (1:V)≤51))
    exact lt_of_lt_of_le (by norm_num : (1:V)<2) he
  have hmod : (1+Exp.exp (51:V))%Exp.exp 51=1 := by
    rw [show (1:V)+Exp.exp 51=1+Exp.exp 51*1 by ring,
      mod_add_mul' _ _ (exp_pos (51:V)),mod_eq_self_of_lt hE]
  have hmask : Exp.exp (51:V)-2=2*(Exp.exp 50-1) := by
    obtain ⟨e,he⟩ : ∃e:V,Exp.exp 50=e+1 :=
      ⟨Exp.exp 50-1,(tsub_add_cancel_of_le (one_le_exp 50)).symm⟩
    rw [show (51:V)=50+1 by norm_num,exp_succ,he,add_tsub_cancel_right,
      show (2:V)*(e+1)=2*e+2 by ring,add_tsub_cancel_right]
  rw [noCarry_iff]
  intro i
  by_cases hi : i<51
  · have heq : fbit (1+Exp.exp (51:V)) i=fbit (1:V) i := by
      have hd := fbit_dig (51:V) (1+Exp.exp 51) 0 i hi
      simpa only [dig_zero_index,hmod,mul_zero,zero_add] using hd.symm
    by_cases h0 : i=0
    · subst i
      rw [hmask,fbit_two_mul_zero_eq_zero]
      simp
    · have hi1 : 1≤i := pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
      have hiE : (1:V)<Exp.exp i := by
        have he : (2:V)≤Exp.exp i := by simpa only [exp_one] using (exp_monotone_le.mpr hi1)
        exact lt_of_lt_of_le (by norm_num : (1:V)<2) he
      rw [heq,fbit_eq_div,div_eq_zero_of_lt _ hiE]
      simp [fbit_le_one]
  · have hi51 : (51:V)≤i := not_lt.mp hi
    have hm : Exp.exp (51:V)-2<Exp.exp i := lt_of_lt_of_le
      (tsub_lt_self (exp_pos _) (by norm_num)) (exp_monotone_le.mpr hi51)
    rw [fbit_eq_div (Exp.exp (51:V)-2) i,div_eq_zero_of_lt _ hm]
    simp [fbit_le_one]
end CompactSelectorConverse
#print axioms CompactSelectorConverse.zero_mask
#print axioms CompactSelectorConverse.one_mask
