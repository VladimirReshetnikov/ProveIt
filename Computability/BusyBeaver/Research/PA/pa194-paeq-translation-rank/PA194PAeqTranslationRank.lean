import PA194PAeqTermRank
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTranslationRank
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessTermFunctions PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termCode_rank : PRAFixpointRank.RankFinite
    ((termConstruction (V := V)).construction ℒₒᵣ) (fun x => x) := by
  intro param C x h
  simp only [Language.TermRec.Construction.construction, Language.TermRec.Construction.Phi] at h ⊢
  rcases h with ⟨ht, h | h | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩⟩
  · exact ⟨ht, Or.inl h⟩
  · exact ⟨ht, Or.inr (Or.inl h)⟩
  · refine ⟨ht, Or.inr (Or.inr ⟨k, f, v, w, ⟨hk, ?_⟩, rfl⟩)⟩
    intro i hi
    refine ⟨hw i hi, ?_⟩
    have hv : IsUTermVec ℒₒᵣ k v := (IsUTerm.func_iff.mp (by simpa using ht)).2
    have hiv : i < len v := by simpa [hv.lh] using hi
    have hiw : i < len w := by simpa [hk] using hi
    have hout : w ≤ functionCode k f w := by
      by_cases hzero : k = 0
      · have hwlen : len w = 0 := hk.symm.trans hzero
        have hw0 : w = 0 := len_zero_iff_eq_nil.mp hwlen
        subst w
        simp
      · simp only [functionCode, if_neg hzero]
        exact (terms_lt_qqFunc 2 (if f = 0 then 2 else 3) w).le
    have ho : w.[i] ≤ (termConstruction (V := V)).func param k f v w := by
      exact le_trans (nth_le w i) hout
    have hin : v.[i] < ^func k f v := nth_lt_qqFunc_of_lt hiv
    exact lt_of_le_of_lt (pair_le_pair_right _ ho) (pair_lt_pair_left hin _)

#print axioms termCode_rank
end PA194PAeqTranslationRank
