import PA194MulCoherenceInduction
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] mulResult orderIso Ordinal.domain

def statement : Form := Ordinal.inductionConclusion property

def applyGlobal {Γ : List Form} (x y b c r s : Nat)
    (h : ND.Proof Γ statement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hc : ND.Proof Γ (Ordinal.domain (.fvar c)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hi : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 coherence (.fvar x)) := by
    convert ND.allElim _ (.fvar x) h using 1 <;>
      (simp only [statement,Ordinal.inductionConclusion,property,coherence,point,premise,mulResult_rew,orderIso_rew,Ordinal.domain_rew,
        Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
        Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
    all_goals simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, mulResult_rew, orderIso_rew,
      Ordinal.domain_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
    all_goals finishSourceSyntax
  exact use x y b c r s (ND.mp hx hi) hy hb hc hxy hbc hr hs
#print axioms applyGlobal
end PA194MulCoherence
