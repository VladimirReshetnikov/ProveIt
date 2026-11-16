import PA194OrderIsoGreatestStatement
import PA194OrdinalStepQuote
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrderIsoGreatestTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def greatestImageBound : Semiproposition M6.PA.RelationalSource.language 5 :=
  orderBijection (.bvar 0) (.bvar 1) (.bvar 2) 🡒
  Ordinal.greatest (.bvar 1) (.bvar 3) 🡒
  edge (.bvar 0) (.bvar 3) (.bvar 4) 🡒 Ordinal.greatest (.bvar 2) (.bvar 4)

theorem greatestImageOpen_fvSup : greatestImageStatement.fvSup = 5 := by decide

theorem greatestImage_closure : greatestImageStatement.univCl = ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [greatestImageOpen_fvSup]
  simp only [allClosure_succ, allClosure_zero, Rew.fixitr_succ, Rew.fixitr_zero, Rew.comp_id]
  change ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ Semiformula.rewAux ((((Rew.fix.comp Rew.fix).comp Rew.fix).comp Rew.fix).comp Rew.fix) greatestImageStatement = _
  simp only [greatestImageStatement,greatestImageBound,sourceImply]
  isoSyntax

#print axioms greatestImageOpen_fvSup
#print axioms greatestImage_closure
end PA194OrderIsoGreatestTemplate
