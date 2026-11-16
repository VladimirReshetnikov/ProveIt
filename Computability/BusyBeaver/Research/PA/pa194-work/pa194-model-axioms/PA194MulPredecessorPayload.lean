import PA194MulPredecessorSeparation
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix mulResult

def separationShift {Γ : List Form} (t : Nat)
    (hsep : ND.Proof Γ (separationFormula (domainEntryProperty (.fvar t)))) :
    ND.Proof (ND.shifted Γ) (separationFormula (domainEntryProperty (.fvar (t+1)))) := by
  convert ND.shiftProof hsep using 1 <;> inclusiveRestrictionSyntax

def resultPayload {n : Nat} (u base out z : Term n) : Formula n :=
  ∃⁰ (Ordinal.zero (Rew.bShift z) ⋏
    (mulPrefix (Rew.bShift u) (Rew.bShift base) (Rew.bShift z) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift u) (Rew.bShift out)))

def predecessorFromPayload {Γ : List Form} (E : FormulaEquality Γ) (t u base out z : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hp : ND.Proof Γ (resultPayload (.fvar u) (.fvar base) (.fvar out) (.fvar z)))
    (hsep : ND.Proof Γ (separationFormula (domainEntryProperty (.fvar t)))) :
    ND.Proof Γ (predecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply ND.exsElim hp
  let σ : Ordinal.Formula 1 := Ordinal.zero (.fvar z) ⋏
    (mulPrefix (.fvar u) (.fvar base) (.fvar z) (.bvar 0) ⋏ edge (.bvar 0) (.fvar u) (.fvar out))
  let C := σ.free :: ND.shifted Γ
  have hd : ND.Proof C (Ordinal.zero (.fvar (z+1)) ⋏
      (mulPrefix (.fvar (u+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0) ⋏ edge (.fvar 0) (.fvar (u+1)) (.fvar (out+1)))) := by
    have hh : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,edge_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have result := predecessorFromSeparation (E.shifted.weaken inc) (t+1) (u+1) (base+1) (z+1) 0 (out+1)
    (ND.weaken (PairGraph.domainShift t ht) inc) (ND.weaken (Ordinal.successorShift t u hs) inc)
    (ND.andLeft hd) (ND.andLeft (ND.andRight hd)) (ND.andRight (ND.andRight hd))
    (ND.weaken (separationShift t hsep) inc)
  convert result using 1 <;> (dsimp [C,σ,predecessorResult] <;>
    simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms separationShift
#print axioms predecessorFromPayload
end PA194MulRecurrenceNew
