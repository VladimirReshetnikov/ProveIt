import PA194FoundationOrdinalInductionMinimal
import PA194OrdinalBaseQuote
namespace PA194DomainGreatestClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def domainGreatestOpen : Form :=
  sourceImply (domain (.fvar 0)) (sourceImply (∼zero (.fvar 0)) (greatestExists (.fvar 0)))

def domainGreatestOpenProof : ND.Proof [] domainGreatestOpen := by
  apply impIntro
  apply impIntro
  let Γ : List Form := ∼zero (.fvar 0) :: domain (.fvar 0) :: []
  have hd : ND.Proof Γ (domain (.fvar 0)) := assumption (by simp [Γ])
  have hn : ND.Proof Γ (∼zero (.fvar 0)) := assumption (by simp [Γ])
  exact domainGreatest 0 hd (notZeroNonempty 0 hn)

def domainGreatestOpenDerivation : LO.FirstOrder.Derivation [domainGreatestOpen] :=
  (domainGreatestOpenProof).contra (by simp [ND.Proof])

def greatestExistsTemplate : Semiproposition M6.PA.RelationalSource.language 1 := greatestExists (.bvar 0)

def domainGreatestBound : Semiproposition M6.PA.RelationalSource.language 1 :=
  sourceImply (domain (.bvar 0)) (sourceImply (∼zero (.bvar 0)) (greatestExists (.bvar 0)))

theorem domainGreatestOpen_fvSup : domainGreatestOpen.fvSup = 1 := by decide

theorem domainGreatest_closure : domainGreatestOpen.univCl = ∀⁰ domainGreatestBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [domainGreatestOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ Semiformula.rewAux Rew.fix domainGreatestOpen = _
  simp only [domainGreatestOpen,domainGreatestBound,sourceImply]
  ordinalSyntax

#print axioms domainGreatestOpenProof
#print axioms domainGreatestOpenDerivation
#print axioms domainGreatestOpen_fvSup
#print axioms domainGreatest_closure
end PA194DomainGreatestClosedTemplate
