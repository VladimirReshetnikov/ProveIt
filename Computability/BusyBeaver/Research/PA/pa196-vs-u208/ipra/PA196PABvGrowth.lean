import PA196PAFormulaComplete
import DiophantineConsistency.PRAWitnessFormulaFunctions

/-! The actual arithmetic-language bound-variable count is bounded by its
formula code in every IΣ₁ model. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PABvGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem termBV_le_self (t : V) : termBV ℒₒᵣ t ≤ t := by
  by_cases ht : IsUTerm ℒₒᵣ t
  · apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
    · definability
    · intro z; simpa using lt_iff_succ_le.mp (var_lt_qqBvar z)
    · intro x; simp
    · intro k f v hkf hv ih
      rw [termBV_func hkf hv]
      have hmax : listMax (termBVVec ℒₒᵣ k v) ≤ v := by
        refine listMaxss_le fun i hi => ?_
        rw [len_termBVVec hv] at hi
        rw [nth_termBVVec hv hi]
        exact le_trans (ih i hi) (nth_le v i)
      exact le_trans hmax (terms_lt_qqFunc k f v).le
  · simp [termBV, IsUTerm.BV.construction, Language.TermRec.Construction.result_prop_not _ _ _ ht]

theorem listMax_termBVVec_le (k v : V) : listMax (termBVVec ℒₒᵣ k v) ≤ v := by
  by_cases hv : IsUTermVec ℒₒᵣ k v
  · refine listMaxss_le fun i hi => ?_
    rw [len_termBVVec hv] at hi
    rw [nth_termBVVec hv hi]
    exact le_trans (termBV_le_self _) (nth_le v i)
  · simp [termBVVec, hv]

theorem termBVVec_le (k v : V) : termBVVec ℒₒᵣ k v ≤ repeatVec v k := by
  by_cases hv : IsUTermVec ℒₒᵣ k v
  · have h := len_repeatVec_of_nth_le (v := termBVVec ℒₒᵣ k v) (m := v)
      (fun i hi => le_trans (nth_le_listMax hi) (listMax_termBVVec_le k v))
    simpa only [len_termBVVec hv] using h
  · simp [termBVVec, hv]

/-- Over `ℒₒᵣ` the bound-variable bound of a formula code is at most the code. -/
theorem bv_le_self (p : V) : bv ℒₒᵣ p ≤ p := by
  by_cases hp : IsUFormula ℒₒᵣ p
  · refine IsUFormula.ISigma1.sigma1_succ_induction (P := fun p => bv ℒₒᵣ p ≤ p) (by definability)
      ?_ ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ p hp
    · intro k r v hr hv
      rw [bv_rel hr hv]; exact le_trans (listMax_termBVVec_le k v) (le_of_lt (v_lt_rel k r v))
    · intro k r v hr hv
      rw [bv_nrel hr hv]; exact le_trans (listMax_termBVVec_le k v) (le_of_lt (v_lt_nrel k r v))
    · intro p q hp hq ihp ihq
      rw [bv_and hp hq]
      exact max_le (le_trans ihp (le_of_lt (lt_K!_left p q))) (le_trans ihq (le_of_lt (lt_K!_right p q)))
    · intro p q hp hq ihp ihq
      rw [bv_or hp hq]
      exact max_le (le_trans ihp (le_of_lt (lt_or_left p q))) (le_trans ihq (le_of_lt (lt_or_right p q)))
    · intro p hp ih
      rw [bv_all hp]; exact le_trans tsub_le_self (le_trans ih (le_of_lt (lt_forall p)))
    · intro p hp ih
      rw [bv_ex hp]; exact le_trans tsub_le_self (le_trans ih (le_of_lt (lt_exists p)))
  · rw [bv_eq_of_not_isUFormula hp]; simp

#print axioms bv_le_self
end PA196PABvGrowth
