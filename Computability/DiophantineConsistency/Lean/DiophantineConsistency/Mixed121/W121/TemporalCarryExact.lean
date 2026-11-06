import DiophantineConsistency.Mixed121.W121.TemporalCarryReset
/-! Width-121 port of `Compact44/TemporalCarryExact` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119, stated for the
width-generic carry family of `Mixed121Rotation` at `w = 121`. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalCarryExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
variable {V ι : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι]

theorem clean_exact (n C T F : V) (a e : ι→V)
    (h : CarryInput 121 n F 1 (Mixed121Rotation.cap (ι:=ι) 121)
      (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T))
    (t : V) (ht : t<n) (hroom : (∑ j, a j*3)+1<Exp.exp 120)
    (hTzero : dig 121 T t=0) (hTpred : dig 121 T (cyc n t 1)≤Exp.exp 120) :
    carry 121 n (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T) (cyc n t 1)=0 ∧
      dig 121 F t = raw 121 (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T) t := by
  have hsum : (∑ j, a j*dig 121 (rot 121 n C (e j%n)) t) ≤ ∑ j, a j*3 := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left
    · exact h.digit_le (Sum.inl j) t ht
    · simp
  have hraw : raw 121 (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T) t ≤ ∑ j, a j*3 := by
    unfold raw
    simp only [Fintype.sum_sum_type,Fintype.sum_unique,Mixed121Rotation.coefficient,
      Mixed121Rotation.word,one_mul,hTzero,add_zero]
    exact hsum
  have hsumlt : (∑ j, a j*3)<Exp.exp 120 :=
    lt_of_le_of_lt (le_add_of_nonneg_right (by simp)) hroom
  have hexp : Exp.exp (120:V)≤Exp.exp 121 := exp_monotone_le.mpr (by norm_num)
  have htarget : raw 121 (Mixed121Rotation.coefficient a) (Mixed121Rotation.word 121 n C e T) t < Exp.exp 121 :=
    lt_of_lt_of_le (lt_of_le_of_lt hraw hsumlt) hexp
  obtain ⟨hz,hd⟩ := W121.TemporalCarryReset.clean n C T F a e h t ht hroom hTpred
  rw [mod_eq_self_of_lt htarget] at hd
  exact ⟨hz,hd⟩
#print axioms W121.TemporalCarryExact.clean_exact
end W121.TemporalCarryExact
