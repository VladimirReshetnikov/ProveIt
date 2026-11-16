import PA194MulRestrictPrevious
import PA194AdditionRestrictionInside
import PA194MulRecurrenceShift
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix

def restrictionRecurrenceAt {Γ : List Form} (E : FormulaEquality Γ) (t g h base i y j : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hc : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar i) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar j) (.fvar i))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar j) (.fvar y)) := by
  have old := restrictionCases t g h i y hr he
  exact restrictPrevious t g h base j y hr
    (restrictionPredecessorInside E t i j ht (ND.andRight old) hs)
    (recurrenceAt g base i y j hc (ND.andLeft old) hs)

def restrictionRecurrence {Γ : List Form} (E : FormulaEquality Γ) (t g h base : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hc : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base))) :
    ND.Proof Γ (mulRecurrence (.fvar h) (.fvar base)) := by
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have tt := PairGraph.domainShift (t+1+1) (PairGraph.domainShift (t+1) (PairGraph.domainShift t ht))
  have rr := graphRestrictionShift (t+1+1) (g+1+1) (h+1+1)
    (graphRestrictionShift (t+1) (g+1) (h+1) (graphRestrictionShift t g h hr))
  have cc := recurrenceShift (g+1+1) (base+1+1) (recurrenceShift (g+1) (base+1) (recurrenceShift g base hc))
  have result : ND.Proof (ND.shifted (ND.shifted (ND.shifted Γ)))
      (sourceImply (edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2))
        (mulPrevious (.fvar (h+1+1+1)) (.fvar (base+1+1+1)) (.fvar 0) (.fvar 1))) := by
    apply ND.impIntro
    let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hp : ND.Proof (q::ND.shifted (ND.shifted (ND.shifted Γ))) q := ND.assumption (by simp)
    let inc := fun p (hp : p ∈ ND.shifted (ND.shifted (ND.shifted Γ))) => List.mem_cons_of_mem q hp
    exact restrictionRecurrenceAt (E.shifted.shifted.shifted.weaken inc)
      (t+1+1+1) (g+1+1+1) (h+1+1+1) (base+1+1+1) 2 1 0
      (ND.up tt q) (ND.up rr q) (ND.up cc q) (ND.andLeft hp) (ND.andRight hp)
  convert result using 1 <;>
    (simp only [mulRecurrence,mulPrevious,Ordinal.successor,Semiformula.free,Rewriting.free,Semiformula.rewAux,edge_rew,addResult_rew,
      Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
      Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three] <;> finishSourceSyntax)
  simp only [addResult_rew,Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app]
  finishSourceSyntax
#print axioms restrictionRecurrenceAt
#print axioms restrictionRecurrence
end PA194MulRecurrenceNew
