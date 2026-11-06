import DiophantineConsistency.Compact44.CompactCarryReset
import DiophantineConsistency.Mixed121.Mixed121Rotation
/-! Width-121 port of `Compact44/TemporalCarryReset` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119, stated for the
width-generic carry family of `Mixed121Rotation` at `w = 121`. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalCarryReset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
variable {V ι : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι]

theorem clean (n C T F : V) (a e : ι→V)
    (h : CarryInput 121 n F 1 (Mixed121Rotation.cap (ι:=ι) 121)
      (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T))
    (t : V) (ht : t<n)
    (hroom : (∑ j, a j*3)+1<Exp.exp 120)
    (hT : dig 121 T (cyc n t 1)≤Exp.exp 120) :
    carry 121 n (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T) (cyc n t 1)=0 ∧
      dig 121 F t = raw 121 (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T) t % Exp.exp 121 := by
  let k := cyc n t 1
  have hk : k<n := cyc_lt h.n_pos _ _
  have hsum : (∑ j, a j * dig 121 (rot 121 n C (e j%n)) k) ≤ ∑ j, a j*3 := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left
    · exact h.digit_le (Sum.inl j) k hk
    · simp
  have hpred : raw 121 (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T) k ≤
      (∑ j, a j*3) + dig 121 T k := by
    unfold raw
    simp only [Fintype.sum_sum_type,Fintype.sum_unique,Mixed121Rotation.coefficient,
      Mixed121Rotation.word,one_mul]
    exact add_le_add hsum (le_refl _)
  have hbase : Exp.exp (120:V)+Exp.exp 120=Exp.exp 121 := by
    rw [show (121:V)=120+1 by norm_num,exp_succ]
    ring
  exact CompactCarryReset.clean_after_bounded_predecessor h ht hpred hT hroom hbase
#print axioms W121.TemporalCarryReset.clean
end W121.TemporalCarryReset
