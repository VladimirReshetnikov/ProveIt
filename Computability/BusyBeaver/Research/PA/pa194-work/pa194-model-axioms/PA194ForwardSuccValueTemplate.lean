import PA194ForwardSuccValueStatement
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ForwardSuccValueTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def successorValueNormalizationBound : Semiproposition M6.PA.RelationalSource.language 2 :=
  sourceIff
    (PA194ForwardTyped.value (PA194PAeq.succ (.bvar 0)) ![.bvar 0] (fun i => .fvar i) (.bvar 1))
    (Ordinal.domain (.bvar 0) ⋏ (Ordinal.domain (.bvar 1) ⋏ Ordinal.successor (.bvar 0) (.bvar 1)))

theorem successorValueOpen_fvSup : successorValueNormalizationStatement.fvSup = 2 := by decide

theorem successorValue_closure : successorValueNormalizationStatement.univCl = ∀⁰ ∀⁰ successorValueNormalizationBound := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [successorValueOpen_fvSup]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  change ∀⁰ ∀⁰ Semiformula.rewAux (Rew.fix.comp Rew.fix) successorValueNormalizationStatement = _
  simp only [successorValueNormalizationStatement,successorValueNormalizationBound,successorVariableValue,
    PA194ForwardTyped.value,PA194PAeq.succ,PA194ForwardTyped.shiftEnv]
  isoSyntax

#print axioms successorValueOpen_fvSup
#print axioms successorValue_closure
end PA194ForwardSuccValueTemplate
