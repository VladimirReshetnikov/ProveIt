import PA194FoundationOrdinalSuccessorDerivation
import PA194OrdinalBaseQuote
namespace PA194DomainSuccessorClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def domainSuccessorOpen : Form := domainSuccessorStatement (.fvar 0)

def domainSuccessorOpenProof : ND.Proof successorAxioms domainSuccessorOpen := domainSuccessorDerivation (.fvar 0)

def domainSuccessorOpenDerivation : LO.FirstOrder.Derivation (successorAxioms.map Semiformula.neg ++ [domainSuccessorOpen]) :=
  domainSuccessorOpenProof.contra (by simp [ND.Proof])

def domainSuccessorBound : Semiproposition M6.PA.RelationalSource.language 1 := domainSuccessorStatement (.bvar 0)

theorem domainSuccessorOpen_fvSup : domainSuccessorOpen.fvSup = 1 := by decide

theorem domainSuccessor_closure : domainSuccessorOpen.univCl = ∀⁰ domainSuccessorBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [domainSuccessorOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ Semiformula.rewAux Rew.fix domainSuccessorOpen = _
  simp only [domainSuccessorOpen,domainSuccessorBound,domainSuccessorStatement,domainSuccessorExists]
  ordinalSyntax

#print axioms domainSuccessorOpenProof
#print axioms domainSuccessorOpenDerivation
#print axioms domainSuccessorOpen_fvSup
#print axioms domainSuccessor_closure
end PA194DomainSuccessorClosedTemplate
