import PA196PABvGrowth
import DiophantineConsistency.PRAWitnessSetTerms

/-! Strong-finite rank for bound-variable recursion on arithmetic terms.
For a function term, each queried child term is strictly smaller, and its
bound-variable result is at most the parent's list maximum. -/
set_option autoImplicit false
namespace PA196PATermBVRank
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rankFinite : PRAFixpointRank.RankFinite
    ((IsUTerm.BV.construction (V := V)).construction ℒₒᵣ) (fun x => x) := by
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
    have hout : w.[i] ≤ listMax w := nth_le_listMax hiw
    have hin : v.[i] < ^func k f v := nth_lt_qqFunc_of_lt hiv
    simp only [IsUTerm.BV.construction]
    exact lt_of_le_of_lt (pair_le_pair_right _ hout) (pair_lt_pair_left hin _)

#print axioms rankFinite
end PA196PATermBVRank
