import PA194MulCoherenceSyntax
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] mulResult orderIso Ordinal.domain point premise

def atIndices {Γ : List Form} (x y b c r s : Nat)
    (h : ND.Proof Γ (coherence (.fvar x))) :
    ND.Proof Γ (point (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  have out := ND.allElim _ (.fvar s) (ND.allElim _ (.fvar r) (ND.allElim _ (.fvar c)
    (ND.allElim _ (.fvar b) (ND.allElim _ (.fvar y) h))))
  convert out using 1 <;>
    (simp only [coherence,point,premise,mulResult_rew,orderIso_rew,Ordinal.domain_rew,Semiformula.free,Rewriting.free,
      Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
      Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
  all_goals simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, mulResult_rew, orderIso_rew,
    Ordinal.domain_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  all_goals finishSourceSyntax

def shift {Γ : List Form} (x : Nat) (h : ND.Proof Γ (coherence (.fvar x))) :
    ND.Proof (ND.shifted Γ) (coherence (.fvar (x+1))) := by
  convert ND.shiftProof h using 1 <;>
    (simp only [coherence,point,premise,mulResult_rew,orderIso_rew,Ordinal.domain_rew,Semiformula.shift,Rewriting.shift,
      Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
      Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
  all_goals simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, mulResult_rew, orderIso_rew,
    Ordinal.domain_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  all_goals finishSourceSyntax
#print axioms atIndices
#print axioms shift
end PA194MulCoherence
