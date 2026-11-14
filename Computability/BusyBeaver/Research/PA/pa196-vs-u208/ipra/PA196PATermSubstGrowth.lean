import PA196PATermBShiftGrowth

/-! Arithmetic term substitution has a uniform double-exponential growth
bound in every IΣ₁ model. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PATermSubstGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessTermFunctions PA196PATermBShiftGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termSubst_le (w t : V) : termSubst ℒₒᵣ w t ≤ tau (w + t + 8) (20 * t + 20) := by
  by_cases ht : IsUTerm ℒₒᵣ t
  · apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
    · definability
    · intro z
      rw [termSubst_bvar]
      apply le_trans (nth_le w z)
      apply le_trans ?_ (le_tau _ _)
      exact le_trans le_self_add le_self_add
    · intro x
      rw [termSubst_fvar]
      apply le_trans ?_ (le_tau _ _)
      exact le_trans le_add_self le_self_add
    · intro k f v hkf hv ih
      rw [termSubst_func hkf hv]
      set P : V := ^func k f v
      have hk : k ≤ 2 := arithmetic_arity_le_two hkf
      have hchild : ∀ i < k, termSubst ℒₒᵣ w v.[i] ≤ tau (w + P + 8) (20 * P) := by
        intro i hi
        have hi' : i < len v := by simpa [hv.lh] using hi
        have hlt : v.[i] < P := nth_lt_qqFunc_of_lt hi'
        have hdepth : 20 * v.[i] + 20 ≤ 20 * P := by
          calc 20 * v.[i] + 20 = 20 * (v.[i] + 1) := by ring
            _ ≤ 20 * P := mul_le_mul' le_rfl (lt_iff_succ_le.mp hlt)
        exact le_trans (ih i hi) (tau_mono (add_le_add (add_le_add le_rfl (le_of_lt hlt)) le_rfl) hdepth)
      have hvec : termSubstVec ℒₒᵣ k w v ≤ repeatVec (tau (w + P + 8) (20 * P)) k := by
        have hh := len_repeatVec_of_nth_le (v := termSubstVec ℒₒᵣ k w v)
          (m := tau (w + P + 8) (20 * P)) (fun i hi => by
            have hi' : i < k := by simpa [len_termSubstVec hv] using hi
            rw [nth_termSubstVec hv hi']
            exact hchild i hi')
        simpa [len_termSubstVec hv] using hh
      have hvbound : termSubstVec ℒₒᵣ k w v ≤ tau (w + P + 8) (20 * P + 4) := by
        apply le_trans hvec
        apply le_trans (repeatVec_le_tau le_rfl k)
        exact tau_mono le_rfl (add_le_add le_rfl (by
          calc 2 * k ≤ 2 * (2 : V) := mul_le_mul' le_rfl hk
            _ = 4 := by norm_num))
      have hc := code4_le_tau
        (le_tau_of (w + P) 2 (20 * P + 4) (small_le (w + P) (by norm_num)))
        (le_tau_of (w + P) k (20 * P + 4)
          (le_trans (arity_lt_qqFunc k f v).le (le_trans le_add_self le_self_add)))
        (le_tau_of (w + P) f (20 * P + 4)
          (le_trans (func_lt_qqFunc k f v).le (le_trans le_add_self le_self_add))) hvbound
      apply le_trans (by simpa [qqFunc] using hc)
      apply tau_mono le_rfl
      calc 20 * P + 4 + 2 + 2 + 2 = 20 * P + 10 := by ring
        _ ≤ 20 * P + 20 := add_le_add le_rfl (by norm_num)
  · simp [termSubst, Language.TermRec.Construction.result_prop_not _ _ _ ht]

#print axioms termSubst_le
end PA196PATermSubstGrowth
