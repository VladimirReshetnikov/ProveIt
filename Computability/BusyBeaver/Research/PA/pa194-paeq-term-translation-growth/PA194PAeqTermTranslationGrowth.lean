import PA194PAeqFormulaValidity
import PA196PATermBShiftGrowth
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194PAeqTermTranslationGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessRepeatVec PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fixedAllowance : V := ((1000 * 1000) * (1000 * 1000)) * (1000 * 1000)
instance fixedAllowance_defined : 𝚺₁-Function₁ (fun _ : V => (fixedAllowance : V)) := by
  unfold fixedAllowance
  definability

theorem termCode_le (t : V) : termCode t ≤ tau (t + fixedAllowance + 8) (20 * t + 20) := by
  by_cases ht : IsUTerm ℒₒᵣ t
  · apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
    · definability
    · intro z
      rw [termCode_bvar]
      exact le_trans (le_trans le_self_add le_self_add) (le_tau _ _)
    · intro x
      rw [termCode_fvar]
      exact le_trans (le_trans le_self_add le_self_add) (le_tau _ _)
    · intro k f v hkf hv ih
      rw [termCode_func hkf hv]
      set P : V := ^func k f v
      have hk : k ≤ 2 := PA196PATermBShiftGrowth.arithmetic_arity_le_two hkf
      by_cases hk0 : k = 0
      · by_cases hf : f = 0
        · simp only [functionCode, hk0,hf,if_pos]
          have hc : (zeroCode : V) ≤ fixedAllowance := by
            norm_num [fixedAllowance,zeroCode,qqFunc,pair]
          exact le_trans hc (le_trans (le_trans (le_add_self : fixedAllowance ≤ P + fixedAllowance) le_self_add) (le_tau _ _))
        · simp only [functionCode, hk0,hf,if_pos,if_false]
          have hc : (PA194PAeqTermBlueprint.oneCode : V) ≤ fixedAllowance := by
            norm_num [fixedAllowance,PA194PAeqTermBlueprint.oneCode,zeroCode,qqFunc,pair,adjoin_def]
          exact le_trans hc (le_trans (le_trans (le_add_self : fixedAllowance ≤ P + fixedAllowance) le_self_add) (le_tau _ _))
      · simp only [functionCode,hk0,if_false]
        have hchild : ∀ i < k, termCode v.[i] ≤ tau (P + fixedAllowance + 8) (20 * P) := by
          intro i hi
          have hi' : i < len v := by simpa [hv.lh] using hi
          have hlt : v.[i] < P := nth_lt_qqFunc_of_lt hi'
          have hdepth : 20 * v.[i] + 20 ≤ 20 * P := by
            calc 20 * v.[i] + 20 = 20 * (v.[i] + 1) := by ring
              _ ≤ 20 * P := mul_le_mul' le_rfl (lt_iff_succ_le.mp hlt)
          exact le_trans (ih i hi) (tau_mono (add_le_add (add_le_add (le_of_lt hlt) le_rfl) le_rfl) hdepth)
        have hvec : termVector k v ≤ repeatVec (tau (P + fixedAllowance + 8) (20 * P)) k := by
          have hh := len_repeatVec_of_nth_le (v := termVector k v)
            (m := tau (P + fixedAllowance + 8) (20 * P)) (fun i hi => by
              have hi' : i < k := by simpa [termVector_length hv] using hi
              rw [termVector_nth hv hi']
              exact hchild i hi')
          simpa [termVector_length hv] using hh
        have hvbound : termVector k v ≤ tau (P + fixedAllowance + 8) (20 * P + 4) := by
          apply le_trans hvec
          apply le_trans (repeatVec_le_tau le_rfl k)
          exact tau_mono le_rfl (add_le_add le_rfl (by
            calc 2 * k ≤ 2 * (2 : V) := mul_le_mul' le_rfl hk
              _ = 4 := by norm_num))
        have hh : (if f = 0 then (2:V) else 3) ≤ tau (P + fixedAllowance + 8) (20 * P + 4) := by
          split_ifs <;> exact le_trans (by norm_num) (four_le_tau _ _)
        have hc := code4_le_tau
          (le_trans (by norm_num : (2:V) ≤ 4) (four_le_tau _ _))
          (le_trans (by norm_num : (2:V) ≤ 4) (four_le_tau _ _)) hh hvbound
        apply le_trans (by simpa [qqFunc] using hc)
        apply tau_mono le_rfl
        calc 20 * P + 4 + 2 + 2 + 2 = 20 * P + 10 := by ring
          _ ≤ 20 * P + 20 := add_le_add le_rfl (by norm_num)
  · simp [termCode_invalid t ht]

theorem termVector_le (k ts : V) :
    termVector k ts ≤ repeatVec (tau (ts + fixedAllowance + 8) (20 * ts + 20)) k := by
  by_cases hv : IsUTermVec ℒₒᵣ k ts
  · have h := len_repeatVec_of_nth_le (v := termVector k ts)
      (m := tau (ts + fixedAllowance + 8) (20 * ts + 20)) (fun i hi => by
        have hi' : i < k := by simpa [termVector_length hv] using hi
        rw [termVector_nth hv hi']
        exact le_trans (termCode_le ts.[i])
          (tau_mono (add_le_add (add_le_add (nth_le ts i) le_rfl) le_rfl)
            (add_le_add (mul_le_mul' le_rfl (nth_le ts i)) le_rfl)))
    simpa [termVector_length hv] using h
  · simp [termVector, (termConstruction (V := V)).resultVec_of_not ℒₒᵣ ![] hv]

#print axioms termVector_le
#print axioms termCode_le
end PA194PAeqTermTranslationGrowth
