import DiophantineConsistency.PRAWitnessCodeGrowth
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Arithmetic bound-variable shifting has an explicit double-exponential
all-model growth bound. Arithmetic function symbols have arity at most two. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PATermBShiftGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessTermFunctions

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arithmetic_arity_le_two {k f : V} (h : (ℒₒᵣ).IsFunc k f) : k ≤ 2 := by
  have h' := h
  simp [Language.IsFunc, Bootstrapping.Arithmetic.func_def_LOR] at h'
  rcases h' with h' | h' | h' | h' <;> rcases h' with ⟨rfl, _⟩ <;> simp

theorem termBShift_le (t : V) : termBShift ℒₒᵣ t ≤ tau (t + 8) (20 * t + 20) := by
  by_cases ht : IsUTerm ℒₒᵣ t
  · apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
    · definability
    · intro z
      rw [termBShift_bvar]
      have hz : z + 1 ≤ ^#z := lt_iff_succ_le.mp (var_lt_qqBvar z)
      have hc := code2_le_tau (le_tau_of (^#z) 0 0 (by simp))
        (le_tau_of (^#z) (z+1) 0 (le_trans hz le_self_add))
      apply le_trans (by simpa [qqBvar] using hc)
      apply tau_mono le_rfl
      exact le_trans (by norm_num) (le_add_self (a := (20 : V)) (b := 20 * ^#z))
    · intro x
      rw [termBShift_fvar]
      exact le_trans (le_trans le_self_add (le_tau _ _))
        (tau_mono le_rfl (le_refl _))
    · intro k f v hkf hv ih
      rw [termBShift_func hkf hv]
      set P : V := ^func k f v
      have hk : k ≤ 2 := arithmetic_arity_le_two hkf
      have hchild : ∀ i < k, termBShift ℒₒᵣ v.[i] ≤ tau (P + 8) (20 * P) := by
        intro i hi
        have hi' : i < len v := by simpa [hv.lh] using hi
        have hlt : v.[i] < P := nth_lt_qqFunc_of_lt hi'
        have hdepth : 20 * v.[i] + 20 ≤ 20 * P := by
          calc 20 * v.[i] + 20 = 20 * (v.[i] + 1) := by ring
            _ ≤ 20 * P := mul_le_mul' le_rfl (lt_iff_succ_le.mp hlt)
        exact le_trans (ih i hi) (tau_mono (add_le_add (le_of_lt hlt) le_rfl) hdepth)
      have hvec : termBShiftVec ℒₒᵣ k v ≤ repeatVec (tau (P + 8) (20 * P)) k := by
        have hh := len_repeatVec_of_nth_le (v := termBShiftVec ℒₒᵣ k v)
          (m := tau (P + 8) (20 * P)) (fun i hi => by
            have hi' : i < k := by simpa [len_termBShiftVec hv] using hi
            rw [nth_termBShiftVec hv hi']
            exact hchild i hi')
        simpa [len_termBShiftVec hv] using hh
      have hvbound : termBShiftVec ℒₒᵣ k v ≤ tau (P + 8) (20 * P + 4) := by
        apply le_trans hvec
        apply le_trans (repeatVec_le_tau le_rfl k)
        exact tau_mono le_rfl (add_le_add le_rfl (by
          calc 2 * k ≤ 2 * (2 : V) := mul_le_mul' le_rfl hk
            _ = 4 := by norm_num))
      have hc := code4_le_tau
        (le_tau_of P 2 (20 * P + 4) (small_le P (by norm_num)))
        (le_tau_of P k (20 * P + 4) (le_trans (arity_lt_qqFunc k f v).le le_self_add))
        (le_tau_of P f (20 * P + 4) (le_trans (func_lt_qqFunc k f v).le le_self_add)) hvbound
      apply le_trans (by simpa [qqFunc] using hc)
      apply tau_mono le_rfl
      calc 20 * P + 4 + 2 + 2 + 2 = 20 * P + 10 := by ring
        _ ≤ 20 * P + 20 := add_le_add le_rfl (by norm_num)
  · simp [termBShift, Language.TermRec.Construction.result_prop_not _ _ _ ht]

#print axioms arithmetic_arity_le_two
#print axioms termBShift_le
end PA196PATermBShiftGrowth
