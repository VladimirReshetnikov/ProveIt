import PA194FoundationOrdinalInductionMinimal
import PA194OrdinalBaseQuote
namespace PA194DomainLeastClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def domainLeastOpen : Form :=
  sourceImply (domain (.fvar 1)) (sourceImply (subset (.fvar 0) (.fvar 1))
    (sourceImply (nonempty (.fvar 0)) (leastExists (.fvar 0))))

def domainLeastOpenProof : ND.Proof [] domainLeastOpen := by
  apply impIntro
  apply impIntro
  apply impIntro
  let Γ : List Form := nonempty (.fvar 0) :: subset (.fvar 0) (.fvar 1) :: domain (.fvar 1) :: []
  have hd : ND.Proof Γ (domain (.fvar 1)) := assumption (by simp [Γ])
  have hs : ND.Proof Γ (subset (.fvar 0) (.fvar 1)) := assumption (by simp [Γ])
  have hn : ND.Proof Γ (nonempty (.fvar 0)) := assumption (by simp [Γ])
  exact andLeft (internalExtremaAt 1 0 (andRight (andRight (andRight (andLeft hd)))) hs hn)

def domainLeastOpenDerivation : LO.FirstOrder.Derivation [domainLeastOpen] :=
  domainLeastOpenProof.contra (by simp [ND.Proof])

def domainLeastBound : Semiproposition M6.PA.RelationalSource.language 2 :=
  sourceImply (domain (.bvar 1)) (sourceImply (subset (.bvar 0) (.bvar 1))
    (sourceImply (nonempty (.bvar 0)) (leastExists (.bvar 0))))

theorem domainLeastOpen_fvSup : domainLeastOpen.fvSup = 2 := by decide

theorem domainLeast_closure : domainLeastOpen.univCl = ∀⁰ ∀⁰ domainLeastBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [domainLeastOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ Semiformula.rewAux (Rew.fix.comp Rew.fix) domainLeastOpen = _
  simp only [domainLeastOpen,domainLeastBound,sourceImply]
  ordinalSyntax

#print axioms domainLeastOpenProof
#print axioms domainLeastOpenDerivation
#print axioms domainLeastOpen_fvSup
#print axioms domainLeast_closure
end PA194DomainLeastClosedTemplate
