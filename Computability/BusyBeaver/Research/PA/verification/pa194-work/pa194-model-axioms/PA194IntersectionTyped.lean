import PA194TypedSchema
import PA194SourceIntersection
set_option maxRecDepth 5000
set_option maxHeartbeats 5000000
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource
theorem intersection_typed_separation : (separationFormula (Ordinal.intersectionProperty (.fvar 0))).univCl =
    Ordinal.intersectionFormula.univCl := by
  apply (Semiformula.coe_inj _ _).mp
  simp only [Semiformula.coe_univCl_eq_univCl']
  have hi : Ordinal.intersectionFormula.freeVariables = ∅ := by decide
  rw [Semiformula.univCl'_eq_self_of _ hi]
  have hs : (separationFormula (Ordinal.intersectionProperty (.fvar 0))).fvSup = 1 := by decide
  unfold Semiformula.univCl'
  rw [hs]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change (∀⁰ Semiformula.rewAux Rew.fix (separationFormula (Ordinal.intersectionProperty (.fvar 0)))) = _
  simp only [separationFormula, Ordinal.intersectionFormula, Ordinal.intersection,
    Ordinal.intersectionProperty, memAtom, liftMember, ND.mem, sourceIff, sourceImply,
    Semiformula.rewAux, Semiformula.neg, Semiformula.neg_eq, Function.comp_def]
  repeat' first
    | rfl
    | (funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    | (change Semiformula.and _ _ = Semiformula.and _ _; congr 1)
    | (change Semiformula.or _ _ = Semiformula.or _ _; congr 1)
    | (change Semiformula.all _ = Semiformula.all _; congr 1)
    | (change Semiformula.exs _ = Semiformula.exs _; congr 1)
    | (change Semiformula.rel _ _ = Semiformula.rel _ _; congr 1)
    | (change Semiformula.nrel _ _ = Semiformula.nrel _ _; congr 1)

#print axioms intersection_typed_separation
