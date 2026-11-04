import DiophantineConsistency.Compact44.CompactCarryReset
import DiophantineConsistency.Compact44.GenericBandCarryFamily
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalCarryReset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
variable {V ι : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι]

theorem clean (n C T F : V) (a e : ι→V)
    (h : CarryInput 67 n F 1 (GenericBandCarryFamily.cap (ι:=ι))
      (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T))
    (t : V) (ht : t<n)
    (hroom : (∑ j, a j*3)+1<Exp.exp 66)
    (hT : dig 67 T (cyc n t 1)≤Exp.exp 66) :
    carry 67 n (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) (cyc n t 1)=0 ∧
      dig 67 F t = raw 67 (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) t % Exp.exp 67 := by
  let k := cyc n t 1
  have hk : k<n := cyc_lt h.n_pos _ _
  have hsum : (∑ j, a j * dig 67 (rot 67 n C (e j%n)) k) ≤ ∑ j, a j*3 := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left
    · exact h.digit_le (Sum.inl j) k hk
    · simp
  have hpred : raw 67 (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) k ≤
      (∑ j, a j*3) + dig 67 T k := by
    unfold raw
    simp only [Fintype.sum_sum_type,Fintype.sum_unique,GenericBandCarryFamily.coefficient,
      GenericBandCarryFamily.word,one_mul]
    exact add_le_add hsum (le_refl _)
  have hbase : Exp.exp (66:V)+Exp.exp 66=Exp.exp 67 := by
    rw [show (67:V)=66+1 by norm_num,exp_succ]
    ring
  exact CompactCarryReset.clean_after_bounded_predecessor h ht hpred hT hroom hbase
#print axioms TemporalCarryReset.clean
end TemporalCarryReset
