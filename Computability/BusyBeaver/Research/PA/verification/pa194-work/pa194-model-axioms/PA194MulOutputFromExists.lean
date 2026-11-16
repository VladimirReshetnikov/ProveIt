import PA194MulOutputFromPrefix
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix mulResult

def outputFromGraphExists {Γ : List Form} (E : FormulaEquality Γ) (x base z : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (prefixGraphExists (.fvar x) (.fvar base) (.fvar z))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar base)) := by
  apply ND.exsElim hp
  let σ : Ordinal.Formula 1 := mulPrefix (.fvar x) (.fvar base) (.fvar z) (.bvar 0)
  let C := σ.free :: ND.shifted Γ
  have hg : ND.Proof C (mulPrefix (.fvar (x+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,mulPrefix_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have out := outputFromPrefix (E.shifted.weaken inc) (x+1) (base+1) (z+1) 0
    (ND.weaken (Ordinal.zeroShift z hz) inc) hg
  convert out using 1 <;> (dsimp [C,σ,mulOutput] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,Rew.shift,Rew.q,Rew.func])

def outputFromExists {Γ : List Form} (E : FormulaEquality Γ) (x base : Nat)
    (hp : ND.Proof Γ (mulPrefixExists (.fvar x) (.fvar base))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar base)) := by
  apply ND.exsElim hp
  let σ : Ordinal.Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    mulPrefix (.fvar x) (.fvar base) (.bvar 1) (.bvar 0))
  let C := σ.free :: ND.shifted Γ
  have hx : ND.Proof C (prefixPayload (.fvar (x+1)) (.fvar (base+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,prefixPayload] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have out := outputFromGraphExists (E.shifted.weaken inc) (x+1) (base+1) 0 (payloadZero _ _ _ hx) (payloadGraph _ _ _ hx)
  convert out using 1 <;> (dsimp [C,σ,mulOutput] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms outputFromGraphExists
#print axioms outputFromExists
end PA194MulRecurrenceNew
