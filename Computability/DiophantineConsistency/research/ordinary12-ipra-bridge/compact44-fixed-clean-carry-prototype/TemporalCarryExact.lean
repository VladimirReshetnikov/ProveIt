import DiophantineConsistency.ConcreteCarryRoom
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalCarryExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
variable {V ι : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι]

theorem clean_exact (n C T F : V) (a e : ι→V)
    (h : CarryInput 67 n F 1 (GenericBandCarryFamily.cap (ι:=ι))
      (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T))
    (t : V) (ht : t<n) (hroom : (∑ j, a j*3)+1<Exp.exp 66)
    (hTzero : dig 67 T t=0) (hTpred : dig 67 T (cyc n t 1)≤Exp.exp 66) :
    carry 67 n (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) (cyc n t 1)=0 ∧
      dig 67 F t = raw 67 (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) t := by
  have hsum : (∑ j, a j*dig 67 (rot 67 n C (e j%n)) t) ≤ ∑ j, a j*3 := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left
    · exact h.digit_le (Sum.inl j) t ht
    · simp
  have hraw : raw 67 (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) t ≤ ∑ j, a j*3 := by
    unfold raw
    simp only [Fintype.sum_sum_type,Fintype.sum_unique,GenericBandCarryFamily.coefficient,
      GenericBandCarryFamily.word,one_mul,hTzero,add_zero]
    exact hsum
  have hsumlt : (∑ j, a j*3)<Exp.exp 66 :=
    lt_of_le_of_lt (le_add_of_nonneg_right (by simp)) hroom
  have hexp : Exp.exp (66:V)≤Exp.exp 67 := exp_monotone_le.mpr (by norm_num)
  have htarget : raw 67 (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word n C e T) t < Exp.exp 67 :=
    lt_of_lt_of_le (lt_of_le_of_lt hraw hsumlt) hexp
  obtain ⟨hz,hd⟩ := TemporalCarryReset.clean n C T F a e h t ht hroom hTpred
  rw [mod_eq_self_of_lt htarget] at hd
  exact ⟨hz,hd⟩
#print axioms TemporalCarryExact.clean_exact
end TemporalCarryExact
