import PA194MulRecurrenceExtensionAt
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult

def recurrenceShift {Γ : List Form} (g base : Nat)
    (hr : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base))) :
    ND.Proof (ND.shifted Γ) (mulRecurrence (.fvar (g+1)) (.fvar (base+1))) := by
  convert ND.shiftProof hr using 1 <;>
    (simp only [mulRecurrence,Ordinal.successor,Semiformula.shift,Rewriting.shift,Semiformula.rewAux,edge_rew,addResult_rew,
      Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
      Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three] <;> finishSourceSyntax)
  simp only [addResult_rew,Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app]
  finishSourceSyntax
#print axioms recurrenceShift
end PA194MulRecurrenceNew
