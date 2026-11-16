import PA194MulPrefixPayload
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix

def prefixExistsStep {Γ : List Form} (E : FormulaEquality Γ) (top u base : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (htop : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefixExists (.fvar top) (.fvar base)))
    (hadd : ND.Proof Γ (additionSupply base)) :
    ND.Proof Γ (mulPrefixExists (.fvar u) (.fvar base)) := by
  apply ND.exsElim hp
  let σ : Ordinal.Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    mulPrefix (.fvar top) (.fvar base) (.bvar 1) (.bvar 0))
  let C := σ.free :: ND.shifted Γ
  have hx : ND.Proof C (prefixPayload (.fvar (top+1)) (.fvar (base+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,prefixPayload] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have out := stepGivenZero (E.shifted.weaken inc) (top+1) (u+1) (base+1) 0
    (ND.weaken (emptyClosedShift hempty) inc) (ND.weaken (adjunctionClosedShift hadj) inc)
    (ND.weaken (PairGraph.domainShift top htop) inc) (ND.weaken (PairGraph.domainShift u hu) inc)
    (ND.weaken (Ordinal.successorShift top u hs) inc) (payloadZero _ _ _ hx) (payloadGraph _ _ _ hx)
    (ND.weaken (supplyShift base hadd) inc)
  convert out using 1 <;> (dsimp [C,σ,mulPrefixExists] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,Rew.shift,Rew.q,Rew.func])
#print axioms prefixExistsStep
end PA194MulRecurrenceNew
