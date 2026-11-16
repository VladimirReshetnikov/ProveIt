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

def predecessorResult {n : Nat} (t base out : Term n) : Formula n :=
  ∃⁰ (Ordinal.domain (.bvar 0) ⋏
    (mulResult (Rew.bShift t) (Rew.bShift base) (.bvar 0) ⋏
      addResult (.bvar 0) (Rew.bShift base) (Rew.bShift out)))

def fromPrefix {Γ : List Form} (t base z g out : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar t) (.fvar base) (.fvar z) (.fvar g)))
    (hv : ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar t) (.fvar out))) :
    ND.Proof Γ (predecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply ND.exsElim hv
  let σ : Ordinal.Formula 1 := edge (.fvar g) (.fvar t) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar base) (.fvar out)
  let C := σ.free :: ND.shifted Γ
  have hd : ND.Proof C (edge (.fvar (g+1)) (.fvar (t+1)) (.fvar 0) ⋏
      addResult (.fvar 0) (.fvar (base+1)) (.fvar (out+1))) := by
    have hh : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,edge_rew,addResult_rew,Rew.free,Rew.q,Rew.func])
  have pp := ND.up (prefixShift t base z g hp) σ.free
  have parts := pp
  unfold mulPrefix at parts
  have dom := graphRangeAt (g+1) (t+1) 0 (ND.andLeft (ND.andRight (ND.andRight parts))) (ND.andLeft hd)
  have res := resultIntro (t+1) (base+1) 0 (z+1) (g+1) (ND.up (Ordinal.zeroShift z hz) σ.free) pp (ND.andLeft hd)
  have result : ND.Proof C (predecessorResult (.fvar (t+1)) (.fvar (base+1)) (.fvar (out+1))) := by
    apply ND.exsIntro _ (.fvar 0)
    convert ND.andIntro dom (ND.andIntro res (ND.andRight hd)) using 1 <;>
      simp [predecessorResult,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.subst,Rew.q,Rew.func]
  convert result using 1 <;> (dsimp [C,σ,predecessorResult] <;>
    simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms fromPrefix
end PA194MulRecurrenceNew
