import PA194MulStepGivenZero
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix

def prefixPayload {n : Nat} (top base z : Term n) : Formula n :=
  ∃⁰ (Ordinal.zero (Rew.bShift z) ⋏ mulPrefix (Rew.bShift top) (Rew.bShift base) (Rew.bShift z) (.bvar 0))

def payloadZero {Γ : List Form} (top base z : Nat)
    (hp : ND.Proof Γ (prefixPayload (.fvar top) (.fvar base) (.fvar z))) :
    ND.Proof Γ (Ordinal.zero (.fvar z)) := by
  apply ND.exsElim hp
  let τ : Ordinal.Formula 1 := Ordinal.zero (.fvar z) ⋏ mulPrefix (.fvar top) (.fvar base) (.fvar z) (.bvar 0)
  have hd : ND.Proof (τ.free :: ND.shifted Γ) (Ordinal.zero (.fvar (z+1)) ⋏
      mulPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof (τ.free :: ND.shifted Γ) τ.free := ND.assumption (by simp)
    convert hh using 1 <;> (dsimp [τ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,Rew.free,Rew.q,Rew.func])
  convert ND.andLeft hd using 1 <;> (dsimp [τ] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.zero_rew,Rew.shift,Rew.q,Rew.func])

def payloadGraph {Γ : List Form} (top base z : Nat)
    (hp : ND.Proof Γ (prefixPayload (.fvar top) (.fvar base) (.fvar z))) :
    ND.Proof Γ (prefixGraphExists (.fvar top) (.fvar base) (.fvar z)) := by
  apply ND.exsElim hp
  let τ : Ordinal.Formula 1 := Ordinal.zero (.fvar z) ⋏ mulPrefix (.fvar top) (.fvar base) (.fvar z) (.bvar 0)
  have hd : ND.Proof (τ.free :: ND.shifted Γ) (Ordinal.zero (.fvar (z+1)) ⋏
      mulPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have hh : ND.Proof (τ.free :: ND.shifted Γ) τ.free := ND.assumption (by simp)
    convert hh using 1 <;> (dsimp [τ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,Rew.free,Rew.q,Rew.func])
  have hi : ND.Proof (τ.free :: ND.shifted Γ)
      ((mulPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.bvar 0))/[.fvar 0]) := by
    convert ND.andRight hd using 1 <;> simp [Semiformula.rewAux,mulPrefix_rew,Rew.subst,Rew.q,Rew.func]
  have out := ND.exsIntro (mulPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.bvar 0)) (.fvar 0) hi
  convert out using 1 <;> (dsimp [τ,prefixGraphExists] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,mulPrefix_rew,Rew.shift,Rew.q,Rew.func])
#print axioms payloadZero
#print axioms payloadGraph
end PA194MulRecurrenceNew
