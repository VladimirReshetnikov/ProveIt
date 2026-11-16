import PA194MulRecurrenceShift
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult

structure Inputs (Γ : List Form) (top u c v g h base : Nat) where
  domain : ND.Proof Γ (Ordinal.domain (.fvar u))
  successor : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u))
  endpoint : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c))
  extension : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v))
  addition : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v))
  recurrence : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base))

def Inputs.weaken {Γ Δ} {top u c v g h base} (I : Inputs Γ top u c v g h base)
    (inc : ∀ p, p ∈ Γ → p ∈ Δ) : Inputs Δ top u c v g h base where
  domain := ND.weaken I.domain inc
  successor := ND.weaken I.successor inc
  endpoint := ND.weaken I.endpoint inc
  extension := ND.weaken I.extension inc
  addition := ND.weaken I.addition inc
  recurrence := ND.weaken I.recurrence inc

def additionShift {Γ : List Form} (x base y : Nat)
    (h : ND.Proof Γ (addResult (.fvar x) (.fvar base) (.fvar y))) :
    ND.Proof (ND.shifted Γ) (addResult (.fvar (x+1)) (.fvar (base+1)) (.fvar (y+1))) := by
  convert ND.shiftProof h using 1
  simp [Semiformula.shift,addResult_rew,Rew.shift,Rew.map]

def Inputs.shift {Γ} {top u c v g h base} (I : Inputs Γ top u c v g h base) :
    Inputs (ND.shifted Γ) (top+1) (u+1) (c+1) (v+1) (g+1) (h+1) (base+1) where
  domain := domainShift u I.domain
  successor := Ordinal.successorShift top u I.successor
  endpoint := edgeShift g top c I.endpoint
  extension := exactShift g h u v I.extension
  addition := additionShift c base v I.addition
  recurrence := recurrenceShift g base I.recurrence

def extension {Γ : List Form} (E : FormulaEquality Γ) (top u c v g h base : Nat)
    (I : Inputs Γ top u c v g h base) :
    ND.Proof Γ (mulRecurrence (.fvar h) (.fvar base)) := by
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have III := I.shift.shift.shift
  have result : ND.Proof (ND.shifted (ND.shifted (ND.shifted Γ)))
      (sourceImply (edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2))
        (mulPrevious (.fvar (h+1+1+1)) (.fvar (base+1+1+1)) (.fvar 0) (.fvar 1))) := by
    apply ND.impIntro
    let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hp : ND.Proof (q::ND.shifted (ND.shifted (ND.shifted Γ))) q := ND.assumption (by simp)
    let inc := fun p (hp : p ∈ ND.shifted (ND.shifted (ND.shifted Γ))) => List.mem_cons_of_mem q hp
    let J := III.weaken inc
    exact extensionAt (E.shifted.shifted.shifted.weaken inc)
      (top+1+1+1) (u+1+1+1) (c+1+1+1) (v+1+1+1) (g+1+1+1) (h+1+1+1) (base+1+1+1) 2 1 0
      J.domain J.successor J.endpoint J.extension J.addition J.recurrence (ND.andLeft hp) (ND.andRight hp)
  convert result using 1 <;>
    (simp only [mulRecurrence,mulPrevious,Ordinal.successor,Semiformula.free,Rewriting.free,Semiformula.rewAux,edge_rew,addResult_rew,
      Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
      Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three] <;> finishSourceSyntax)
  simp only [addResult_rew,Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app]
  finishSourceSyntax
#print axioms additionShift
#print axioms extension
end PA194MulRecurrenceNew
