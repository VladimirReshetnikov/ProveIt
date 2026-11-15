import PA194IsoMatchStatement
import PA194OrdinalStepQuote
set_option maxHeartbeats 5000000
namespace PA194IsoMatchTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def isoMatchBound : Semiproposition M6.PA.RelationalSource.language 3 :=
  Ordinal.domain (.bvar 1) 🡒 Ordinal.successor (.bvar 2) (.bvar 0) 🡒
  orderIso (.bvar 0) (.bvar 1) 🡒 isoPredecessorMatch (.bvar 2) (.bvar 1)

theorem isoMatchOpen_fvSup : isoMatchStatement.fvSup = 3 := by decide

theorem isoMatch_closure : isoMatchStatement.univCl = ∀⁰ ∀⁰ ∀⁰ isoMatchBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [isoMatchOpen_fvSup]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  change ∀⁰ ∀⁰ ∀⁰ Semiformula.rewAux ((Rew.fix.comp Rew.fix).comp Rew.fix) isoMatchStatement = _
  simp only [isoMatchStatement,isoMatchBound,isoPredecessorMatch]
  isoSyntax

#print axioms isoMatchOpen_fvSup
#print axioms isoMatch_closure
end PA194IsoMatchTemplate
