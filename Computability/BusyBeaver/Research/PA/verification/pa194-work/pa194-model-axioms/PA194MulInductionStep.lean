import PA194MulInductionBase
import PA194MulPrefixExistsStep
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix

def inductionStep {Γ : List Form} (E : FormulaEquality Γ) (base : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hadd : ND.Proof Γ (additionSupply base)) :
    ND.Proof Γ (Ordinal.inductionStep (property base)) := by
  apply ND.allIntro
  apply ND.allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ mulPrefixExists (.fvar 1) (.fvar (base+1+1))))
  have hd : ND.Proof (d :: ND.shifted (ND.shifted Γ)) d := ND.assumption (by simp)
  let inc : ∀ p, p ∈ ND.shifted (ND.shifted Γ) → p ∈ d :: ND.shifted (ND.shifted Γ) := fun p hp => List.mem_cons_of_mem d hp
  have out := prefixExistsStep (E.shifted.shifted.weaken inc) 1 0 (base+1+1)
    (ND.weaken (emptyClosedShift (emptyClosedShift hempty)) inc)
    (ND.weaken (adjunctionClosedShift (adjunctionClosedShift hadj)) inc)
    (ND.andLeft hd) (ND.andLeft (ND.andRight hd))
    (ND.andLeft (ND.andRight (ND.andRight hd))) (ND.andRight (ND.andRight (ND.andRight hd)))
    (ND.weaken (supplyShift (base+1) (supplyShift base hadd)) inc)
  have h := ND.impIntro out
  convert h using 1 <;> (dsimp [d,Ordinal.inductionStep,Ordinal.traceProperty,property,mulPrefixExists] <;>
    simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,Rew.free,Rew.q,Rew.func] <;> finishSourceSyntax)
  simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, mulPrefix_rew, Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  finishSourceSyntax
#print axioms inductionStep
end PA194MulRecurrenceNew
