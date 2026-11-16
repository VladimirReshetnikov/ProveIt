import PA194MulCoherenceZeroPoint
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] mulResult orderIso Ordinal.domain

def zeroCase {Γ : List Form} (E : FormulaEquality Γ) (x : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (coherence (.fvar x)) := by
  unfold coherence
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h0 := Ordinal.zeroShift x hz
  have h1 := Ordinal.zeroShift (x+1) h0
  have h2 := Ordinal.zeroShift (x+1+1) h1
  have h3 := Ordinal.zeroShift (x+1+1+1) h2
  have h4 := Ordinal.zeroShift (x+1+1+1+1) h3
  have out := zeroPoint E.shifted.shifted.shifted.shifted.shifted (x+1+1+1+1+1) 4 3 2 1 0 h4
  convert out using 1 <;>
    (simp only [point,premise,mulResult_rew,orderIso_rew,Ordinal.domain_rew,Semiformula.free,Rewriting.free,
      Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
      Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
  all_goals simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, mulResult_rew, orderIso_rew,
    Ordinal.domain_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  all_goals finishSourceSyntax
#print axioms zeroCase
end PA194MulCoherence
