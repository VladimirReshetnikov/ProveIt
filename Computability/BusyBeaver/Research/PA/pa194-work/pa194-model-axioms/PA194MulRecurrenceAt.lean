import PA194MulPreviousPreserve
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult

def recurrenceAt {Γ : List Form} (g base x y z : Nat)
    (hr : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar z) (.fvar y)) := by
  have hi : ND.Proof Γ (sourceImply (edge (.fvar g) (.fvar x) (.fvar y) ⋏
      Ordinal.successor (.fvar z) (.fvar x)) (mulPrevious (.fvar g) (.fvar base) (.fvar z) (.fvar y))) := by
    convert ND.allElim _ (.fvar z) (ND.allElim _ (.fvar y) (ND.allElim _ (.fvar x) hr)) using 1 <;>
      (simp only [mulRecurrence,mulPrevious,Semiformula.rewAux,edge_rew,addResult_rew,
        Ordinal.successor_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
        Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three] <;> finishSourceSyntax)
    simp only [addResult_rew,Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app]
    finishSourceSyntax
  exact ND.mp (ND.andIntro he hs) hi
#print axioms recurrenceAt
end PA194MulRecurrenceNew
