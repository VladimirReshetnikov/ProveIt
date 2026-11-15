import PA194FoundationOrdinalInductionMembers
import PA194FoundationOrdinalInductionNumeric
import PA194OrdinalStepQuote
namespace PA194MemberDomainClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def memberDomainOpen : Form :=
  sourceImply (domain (.fvar 1)) (sourceImply (mem (.fvar 1) (.fvar 0)) (domain (.fvar 0)))

def memberDomainOpenProof : ND.Proof [] memberDomainOpen := by
  apply impIntro
  apply impIntro
  apply memberDomain 1 0
  · exact assumption (by simp)
  · exact assumption (by simp)

def memberDomainOpenDerivation : LO.FirstOrder.Derivation [memberDomainOpen] :=
  (memberDomainOpenProof).contra (by simp [ND.Proof])

open PA194OrdinalStepQuote

def memberDomainBound : Semiproposition M6.PA.RelationalSource.language 2 :=
  let membership := Semiformula.rel Relation.mem ![#0,#1]
  domainOne 🡒 (membership 🡒 domainZero)

theorem memberDomainOpen_fvSup : memberDomainOpen.fvSup = 2 := by decide

theorem memberDomain_closure : memberDomainOpen.univCl = ∀⁰ ∀⁰ memberDomainBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [memberDomainOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ Semiformula.rewAux (Rew.fix.comp Rew.fix) memberDomainOpen = _
  simp only [memberDomainOpen,memberDomainBound,domainOne,domainZero,sourceImply]
  ordinalSyntax

#print axioms memberDomainOpen_fvSup
#print axioms memberDomain_closure
#print axioms memberDomainOpenProof
#print axioms memberDomainOpenDerivation
end PA194MemberDomainClosedTemplate
