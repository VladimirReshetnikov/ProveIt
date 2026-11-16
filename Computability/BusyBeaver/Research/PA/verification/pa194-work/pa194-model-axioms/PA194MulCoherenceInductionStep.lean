import PA194MulCoherenceSuccessorAll
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] mulResult orderIso Ordinal.domain Ordinal.successor

def inductionStep {Γ : List Form} (E : FormulaEquality Γ)
    (haddition : ND.Proof Γ addCoherenceStatement)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation) (hinclusive : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (Ordinal.inductionStep property) := by
  apply ND.allIntro
  apply ND.allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ coherence (.fvar 1)))
  have hd : ND.Proof (d :: ND.shifted (ND.shifted Γ)) d := ND.assumption (by simp)
  let inc : ∀ z, z ∈ ND.shifted (ND.shifted Γ) → z ∈ d :: ND.shifted (ND.shifted Γ) := fun z hz => List.mem_cons_of_mem d hz
  have hstrict' : ND.Proof (ND.shifted (ND.shifted Γ)) closedStrictSeparation := by
    simpa only [PA194CancelClosedShift.closedStrictSeparation_shift] using ND.shiftProof (ND.shiftProof hstrict)
  have hinclusive' : ND.Proof (ND.shifted (ND.shifted Γ)) closedInclusiveSeparation := by
    simpa only [PA194InclusiveSeparationClosure.closedSep_shift] using ND.shiftProof (ND.shiftProof hinclusive)
  let I : StepFrame (d :: ND.shifted (ND.shifted Γ)) 1 0 :=
    ⟨ND.weaken (additionClosedShift (additionClosedShift haddition)) inc,E.shifted.shifted.weaken inc,
      ND.weaken (emptyClosedShift (emptyClosedShift hempty)) inc,
      ND.weaken (adjunctionClosedShift (adjunctionClosedShift hadj)) inc,
      ND.weaken hstrict' inc,ND.weaken hinclusive' inc,ND.andLeft hd,
      ND.andLeft (ND.andRight (ND.andRight hd)),ND.andRight (ND.andRight (ND.andRight hd))⟩
  have h := ND.impIntro (successor 1 0 I)
  convert h using 1 <;> (dsimp [d,Ordinal.inductionStep,Ordinal.traceProperty,property,coherence] <;>
    simp only [point,premise,mulResult_rew,orderIso_rew,Ordinal.domain_rew,Ordinal.successor_rew,
      Semiformula.free,Rewriting.free,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
      Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
  all_goals simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, mulResult_rew, orderIso_rew,
    Ordinal.domain_rew,Ordinal.successor_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  all_goals finishSourceSyntax
#print axioms inductionStep
end PA194MulCoherence
