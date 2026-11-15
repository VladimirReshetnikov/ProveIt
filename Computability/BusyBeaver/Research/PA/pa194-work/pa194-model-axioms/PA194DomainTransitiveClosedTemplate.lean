import PA194FoundationOrdinalInductionMinimal
import PA194OrdinalStepQuote
namespace PA194DomainTransitiveClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def domainTransOpen : Form :=
  sourceImply (domain (.fvar 2)) (sourceImply (mem (.fvar 2) (.fvar 1))
    (sourceImply (mem (.fvar 1) (.fvar 0)) (mem (.fvar 2) (.fvar 0))))

def domainTransOpenProof : ND.Proof [] domainTransOpen := by
  apply impIntro
  apply impIntro
  apply impIntro
  let Γ : List Form := mem (.fvar 1) (.fvar 0) :: mem (.fvar 2) (.fvar 1) :: domain (.fvar 2) :: []
  have hd : ND.Proof Γ (domain (.fvar 2)) := assumption (by simp [Γ])
  exact transitiveAt 2 1 0 (andLeft (andLeft hd)) (assumption (by simp [Γ])) (assumption (by simp [Γ]))

def domainTransOpenDerivation : LO.FirstOrder.Derivation [domainTransOpen] :=
  (domainTransOpenProof).contra (by simp [ND.Proof])

def domainTransBound : Semiproposition M6.PA.RelationalSource.language 3 :=
  sourceImply (domain (.bvar 2)) (sourceImply (mem (.bvar 2) (.bvar 1))
    (sourceImply (mem (.bvar 1) (.bvar 0)) (mem (.bvar 2) (.bvar 0))))

theorem domainTransOpen_fvSup : domainTransOpen.fvSup = 3 := by decide

theorem domainTrans_closure : domainTransOpen.univCl = ∀⁰ ∀⁰ ∀⁰ domainTransBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [domainTransOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ ∀⁰ Semiformula.rewAux ((Rew.fix.comp Rew.fix).comp Rew.fix) domainTransOpen = _
  simp only [domainTransOpen,domainTransBound,sourceImply]
  ordinalSyntax

#print axioms domainTransOpenProof
#print axioms domainTransOpenDerivation
#print axioms domainTransOpen_fvSup
#print axioms domainTrans_closure
end PA194DomainTransitiveClosedTemplate
