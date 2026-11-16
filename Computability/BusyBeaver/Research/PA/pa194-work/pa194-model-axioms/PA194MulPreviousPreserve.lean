import PA194MulRecurrenceNew
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult

def preservePrevious {Γ : List Form} (g h a b base x y : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hp : ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar x) (.fvar y)) := by
  apply ND.exsElim hp
  let σ : Ordinal.Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar base) (.fvar y)
  let C := σ.free :: ND.shifted Γ
  have hc : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0) ⋏
      addResult (.fvar 0) (.fvar (base+1)) (.fvar (y+1))) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,edge_rew,addResult_rew,Rew.free,Rew.q,Rew.func])
  have he := exactPreservesEdge (g+1) (h+1) (a+1) (b+1) (x+1) 0
    (ND.up (exactShift g h a b hx) σ.free) (ND.andLeft hc)
  have out := previousIntro (h+1) (base+1) (x+1) (y+1) 0 he (ND.andRight hc)
  convert out using 1 <;> (dsimp [C,σ,mulPrevious] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,edge_rew,addResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms preservePrevious
end PA194MulRecurrenceNew
