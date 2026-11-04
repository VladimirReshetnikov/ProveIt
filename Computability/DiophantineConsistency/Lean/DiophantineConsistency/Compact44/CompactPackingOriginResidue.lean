import DiophantineConsistency.Compact44.CompactLowModFour
import DiophantineConsistency.ArithmeticMaskPopulation
import DiophantineConsistency.ArithmeticPacking

/-! The low packing condition itself forces the rank's origin residue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPackingOriginResidue
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticRepunit ArithmeticMaskPopulation ArithmeticPacking
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem packing_origin_mod_four {K high N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 590069 K (CompactConcreteIncrement.mask : V) high N s X) :
    (Cw 590069 N X-1)%4=0 := by
  let L : V := CompactConcreteIncrement.mask
  let J : V := rep 590069 N
  obtain ⟨j,hj⟩ := rep_eight (590069:V) N (by norm_num) (N_pos h)
  have hJ4 : J%4=1 := by
    rw [show J=rep 590069 N from rfl,hj,show (8:V)*j+1=1+4*(2*j) by ring,
      mod_add_mul' _ _ (by norm_num),mod_eq_self_of_lt (by norm_num : (1:V)<4)]
  have hmask : (L*J+1)%4=3 := by
    rw [mod_add (by norm_num : (0:V)<4), mod_mul (by norm_num : (0:V)<4),
      show L%4=2 from CompactLowModFour.low_mod_four, hJ4]
    norm_num
  have he2 : Exp.exp (2:V)=4 := by
    rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
    norm_num
  have hnc := noCarry_dig (2:V) (Cw 590069 N X-1) (L*J+1) 0 (packing_low_mask h)
  rw [dig_zero_index, dig_zero_index, he2, hmask] at hnc
  have hthree : (4:V)-1=3 := by
    rw [show (4:V)=3+1 by norm_num, add_tsub_cancel_right]
  have hz := noCarry_ones (2:V) ((Cw 590069 N X-1)%4)
    (by rw [he2]; exact mod_lt _ (by norm_num))
    (by simpa only [he2, hthree] using hnc)
  exact hz

#print axioms CompactPackingOriginResidue.packing_origin_mod_four
end CompactPackingOriginResidue
