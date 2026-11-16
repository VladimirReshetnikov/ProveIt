import PA194MulPrefixZero
import PA194FoundationOrdinalInductionUniform
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix

def property (base : Nat) : Ordinal.Formula 1 := mulPrefixExists (.bvar 0) (.fvar base)

def inductionBase {Γ : List Form} (E : FormulaEquality Γ) (base : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (Ordinal.inductionBase (property base)) := by
  apply ND.allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d :: ND.shifted Γ) d := ND.assumption (by simp)
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ d :: ND.shifted Γ := fun p hp => List.mem_cons_of_mem d hp
  have out := zeroPrefixWitness (E.shifted.weaken inc) 0 (base+1) (ND.andRight hd)
    (ND.weaken (emptyClosedShift hempty) inc) (ND.weaken (adjunctionClosedShift hadj) inc)
  have h := ND.impIntro out
  convert h using 1 <;> (dsimp [d,Ordinal.inductionBase,property,mulPrefixExists] <;>
    simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Semiformula.rewAux_neg,Semiformula.imp_eq,Ordinal.domain_rew,Ordinal.zero_rew,mulPrefix_rew,Rew.free,Rew.q,Rew.func])
  simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, Semiformula.rewAux, Ordinal.domain_rew, Ordinal.zero_rew, Rew.free, Rew.q, Rew.func]
  finishSourceSyntax
#print axioms inductionBase
end PA194MulRecurrenceNew
