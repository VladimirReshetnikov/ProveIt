import PA194IsoCancelStatement
import PA194OrdinalStepQuote
set_option maxHeartbeats 5000000
namespace PA194IsoCancelTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def isoCancelBound : Semiproposition M6.PA.RelationalSource.language 4 :=
  Ordinal.domain (.bvar 1) 🡒 Ordinal.successor (.bvar 2) (.bvar 0) 🡒
  Ordinal.successor (.bvar 3) (.bvar 1) 🡒 orderIso (.bvar 0) (.bvar 1) 🡒
  orderIso (.bvar 2) (.bvar 3)

theorem isoCancelOpen_fvSup : isoCancelStatement.fvSup = 4 := by decide

theorem isoCancel_closure : isoCancelStatement.univCl = ∀⁰ ∀⁰ ∀⁰ ∀⁰ isoCancelBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [isoCancelOpen_fvSup]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  change ∀⁰ ∀⁰ ∀⁰ ∀⁰ Semiformula.rewAux (((Rew.fix.comp Rew.fix).comp Rew.fix).comp Rew.fix) isoCancelStatement = _
  simp only [isoCancelStatement,isoCancelBound]
  isoSyntax

#print axioms isoCancelOpen_fvSup
#print axioms isoCancel_closure
end PA194IsoCancelTemplate
