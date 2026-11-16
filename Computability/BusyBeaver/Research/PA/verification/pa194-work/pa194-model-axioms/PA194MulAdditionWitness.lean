import PA194MulGraphExtension
import PA194FoundationAdditionOutputTotal
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix

def fromEndpoint {Γ : List Form} (E : FormulaEquality Γ) (top u base z g c : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (htop : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (ha : ND.Proof Γ (addOutput (.fvar c) (.fvar base))) :
    ND.Proof Γ (prefixGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  apply ND.exsElim ha
  let σ : Ordinal.Formula 1 := Ordinal.domain (.bvar 0) ⋏ addResult (.fvar c) (.fvar base) (.bvar 0)
  let C := σ.free :: ND.shifted Γ
  have hh : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      addResult (.fvar (c+1)) (.fvar (base+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.domain_rew,addResult_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have out := fromOutputs (E.shifted.weaken inc) (top+1) (u+1) (base+1) (z+1) (g+1) (c+1) 0
    (ND.weaken (emptyClosedShift hempty) inc) (ND.weaken (adjunctionClosedShift hadj) inc)
    (ND.weaken (PairGraph.domainShift top htop) inc) (ND.weaken (PairGraph.domainShift u hu) inc) (ND.andLeft hh)
    (ND.weaken (Ordinal.successorShift top u hs) inc) (ND.weaken (prefixShift top base z g hp) inc)
    (ND.weaken (edgeShift g top c he) inc) (ND.andRight hh)
  convert out using 1 <;> (dsimp [C,σ,prefixGraphExists] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,mulPrefix_rew,Rew.shift,Rew.q,Rew.func])
#print axioms fromEndpoint
end PA194MulRecurrenceNew
