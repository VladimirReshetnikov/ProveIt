import PA194ValueDomain
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

theorem guarded_valBody_domain {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) (j : V) :
    GDerivable T (insert (neg SourceL (substs1 SourceL (^&j) (valBody s)))
      (insert (domainCode (^&j)) (∅ : V))) := by
  obtain ⟨r,hr,hvalid⟩ := valBody_has_domain s hs
  have hd : IsFormula SourceL (domainCode (^&j : V)) := domainCode_valid (by simp)
  have hh : IsFormula SourceL (substs1 SourceL (^&j) r) := IsSemiformula.substs1 (by simp) hvalid
  have hnD : IsFormula SourceL (neg SourceL (domainCode (^&j : V))) := IsSemiformula.neg_iff.mpr hd
  have hnR : IsFormula SourceL (neg SourceL (substs1 SourceL (^&j) r)) := IsSemiformula.neg_iff.mpr hh
  have hOr : IsFormula SourceL (neg SourceL (domainCode (^&j : V)) ^⋎
      neg SourceL (substs1 SourceL (^&j) r)) := IsSemiformula.or.mpr ⟨hnD,hnR⟩
  rw [hr,substs1_domain_and hvalid j,neg_and hd.isUFormula hh.isUFormula]
  apply GDerivable.or_m (p := neg SourceL (domainCode (^&j)))
    (q := neg SourceL (substs1 SourceL (^&j) r)) (by simp)
  apply GDerivable.em (fs_cons hnD (fs_cons hnR (fs_cons hOr (fs_cons hd fs_nil)))) (domainCode (^&j)) <;> simp
#print axioms guarded_valBody_domain
end generic
end PA194GuardedCompiler
