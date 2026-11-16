import PA194MulOutputEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix mulResult

def outputFromPrefix {Γ : List Form} (E : FormulaEquality Γ) (x base z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar x) (.fvar base) (.fvar z) (.fvar g))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar base)) := by
  have hpParts := hp
  unfold mulPrefix at hpParts
  have hd := graphDomainAt x g x (ND.andLeft hpParts)
  have ho := ND.mp (ND.orRight (E.reflexive (.fvar x))) (ND.andRight hd)
  apply ND.exsElim ho
  let σ : Ordinal.Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: ND.shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,edge_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have out := outputFromEndpoint (x+1) (base+1) 0 (z+1) (g+1)
    (ND.weaken (Ordinal.zeroShift z hz) inc) (ND.weaken (prefixShift x base z g hp) inc) he
  convert out using 1 <;> (dsimp [C,σ,mulOutput] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms outputFromPrefix
end PA194MulRecurrenceNew
