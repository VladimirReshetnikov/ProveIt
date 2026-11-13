import DiophantineConsistency.CompactHeterogeneousCarry

/-! A Boolean family with small coefficient mass has zero cyclic carries. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactBooleanZeroCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticWindowDigits
  DiophantineConsistency.ArithmeticCyclicWord
  DiophantineConsistency.CompactHeterogeneousCarry

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {ι : Type*} [Fintype ι]

/-- Strengthen any represented cyclic carry input to cap one and carry zero,
when every source digit is Boolean and the total coefficient mass fits. -/
theorem boolean_zero_carry {w n F b : V} {D a X : ι → V}
    (h : CarryInput w n F b D a X)
    (hbool : ∀ i, ∀ k < n, dig w (X i) k ≤ 1)
    (hmass : (∑ i, a i) + 1 ≤ Exp.exp w - 1) :
    ∀ k < n, carry w n a X k = 0 ∧ dig w F k = raw w a X k := by
  have h0 : CarryInput w n F 0 (fun _ => 1) a X := by
    refine ⟨h.n_pos, h.M_pos, h.word_lt, hbool, h.F_lt, h.congr, ?_⟩
    simpa only [mul_one, zero_add, one_mul] using hmass
  have hz : ∀ k < n, carry w n a X k = 0 := by
    intro k hk
    exact le_antisymm (carry_le h0 hk) (Arithmetic.zero_le _)
  intro k hk
  have hraw : raw w a X k ≤ ∑ i, a i := by
    unfold raw
    calc
      (∑ i, a i * dig w (X i) k) ≤ ∑ i, a i * 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hbool i k hk) (Arithmetic.zero_le _)
      _ = ∑ i, a i := by simp
  have hlt : raw w a X k < Exp.exp w := by
    have ht : (∑ i, a i) < Exp.exp w :=
      lt_of_lt_of_le (lt_add_one _) (le_trans hmass tsub_le_self)
    exact lt_of_le_of_lt hraw ht
  have hprev := hz (cyc n k 1) (cyc_lt h.n_pos k 1)
  have hd := (carry_column h0 hk).2
  rw [hprev, add_zero, mod_eq_self_of_lt hlt] at hd
  exact ⟨hz k hk, hd⟩

#print axioms CompactBooleanZeroCarry.boolean_zero_carry
end CompactBooleanZeroCarry
