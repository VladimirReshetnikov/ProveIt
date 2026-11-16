import PA194MulPredecessorPayload
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix mulResult

def resultPredecessor {Γ : List Form} (E : FormulaEquality Γ) (t u base out : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hp : ND.Proof Γ (mulResult (.fvar u) (.fvar base) (.fvar out)))
    (hsep : ND.Proof Γ (separationFormula (domainEntryProperty (.fvar t)))) :
    ND.Proof Γ (predecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  have hpParts := hp
  unfold mulResult at hpParts
  apply ND.exsElim hpParts
  let σ : Ordinal.Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (.fvar u) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar u) (.fvar out)))
  let C := σ.free :: ND.shifted Γ
  have hd : ND.Proof C (resultPayload (.fvar (u+1)) (.fvar (base+1)) (.fvar (out+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,resultPayload] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,edge_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have result := predecessorFromPayload (E.shifted.weaken inc) (t+1) (u+1) (base+1) (out+1) 0
    (ND.weaken (PairGraph.domainShift t ht) inc) (ND.weaken (Ordinal.successorShift t u hs) inc) hd
    (ND.weaken (separationShift t hsep) inc)
  convert result using 1 <;> (dsimp [C,σ,predecessorResult] <;>
    simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms resultPredecessor
end PA194MulRecurrenceNew
