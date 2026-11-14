import PA194PAeqFormulaCode
import DiophantineConsistency.PRAWitnessTermFunctions
import DiophantineConsistency.PRAWitnessSetTerms

/-! A general identity-rank criterion for arithmetic term recursions whose
function-node output bounds every child output. -/
set_option autoImplicit false
namespace PA194PAeqTermRank
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {ar : ℕ} {β : Language.TermRec.Blueprint ar}

theorem rankFinite (c : Language.TermRec.Construction V β)
    (hf : ∀ param k f v w, listMax w ≤ c.func param k f v w) :
    PRAFixpointRank.RankFinite (c.construction L) (fun x => x) := by
  intro param C x h
  simp only [Language.TermRec.Construction.construction, Language.TermRec.Construction.Phi] at h ⊢
  rcases h with ⟨ht, h | h | ⟨k, f, v, w, ⟨hk, hw⟩, rfl⟩⟩
  · exact ⟨ht, Or.inl h⟩
  · exact ⟨ht, Or.inr (Or.inl h)⟩
  · refine ⟨ht, Or.inr (Or.inr ⟨k, f, v, w, ⟨hk, ?_⟩, rfl⟩)⟩
    intro i hi
    refine ⟨hw i hi, ?_⟩
    have hv : IsUTermVec L k v := (IsUTerm.func_iff.mp (by simpa using ht)).2
    have hiv : i < len v := by simpa [hv.lh] using hi
    have hiw : i < len w := by simpa [hk] using hi
    have hout : w.[i] ≤ c.func param k f v w := le_trans (nth_le_listMax hiw) (hf param k f v w)
    have hin : v.[i] < ^func k f v := nth_lt_qqFunc_of_lt hiv
    exact lt_of_le_of_lt (pair_le_pair_right _ hout) (pair_lt_pair_left hin _)

theorem target_bShift_rank : PRAFixpointRank.RankFinite
    ((TermBShift.construction (V := V)).construction PA194PAeq.language) (fun x => x) := by
  apply rankFinite
  intro param k f v w
  exact le_trans (PRAWitnessTermFunctions.listMax_le_self w) (terms_lt_qqFunc k f w).le

theorem target_subst_rank : PRAFixpointRank.RankFinite
    ((TermSubst.construction (V := V)).construction PA194PAeq.language) (fun x => x) := by
  apply rankFinite
  intro param k f v w
  exact le_trans (PRAWitnessTermFunctions.listMax_le_self w) (terms_lt_qqFunc k f w).le

#print axioms target_bShift_rank
#print axioms target_subst_rank
#print axioms rankFinite
end PA194PAeqTermRank
