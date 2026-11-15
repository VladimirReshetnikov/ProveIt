import PA194AdjunctionSourceSyntax
import PA194TypedSchema
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND
open scoped LO.FirstOrder

theorem swapped_adjunction_closure :
    (ND.adjunctionExists (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)).univCl = adjunctionFormula.univCl := by
  apply (Semiformula.coe_inj _ _).mp
  simp only [Semiformula.coe_univCl_eq_univCl']
  have hi : adjunctionFormula.freeVariables = ∅ := by decide
  rw [Semiformula.univCl'_eq_self_of _ hi]
  have hs : (ND.adjunctionExists (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)).fvSup = 2 := by decide
  unfold Semiformula.univCl'
  rw [hs]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ Semiformula.rewAux (Rew.fix.comp Rew.fix) (ND.adjunctionExists (.fvar 1 : ND.Term) (.fvar 0 : ND.Term)) = _
  simp only [adjunctionFormula, ND.adjunctionExists, ND.adjunctionInstance, ND.property,
    ND.mem, ND.eq, sourceIff,sourceImply, memAtom,eqAtom, Semiformula.rewAux,
    Semiformula.neg, Semiformula.neg_eq, Function.comp_def]
  finishSourceSyntax

#print axioms swapped_adjunction_closure
end M6.PA.RelationalSource.Ordinal
