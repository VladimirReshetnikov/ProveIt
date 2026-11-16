import PA194AdditionCoherenceRules
import PA194FoundationOrdinalInductionSchema
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain

def addCoherenceStatement : Form := Ordinal.inductionConclusion addCoherenceProperty

macro "coherenceInductionSyntax" : tactic => `(tactic|
  (simp only [Ordinal.inductionBase,Ordinal.inductionStep,Ordinal.inductionConclusion,
    Ordinal.traceProperty,addCoherence,addCoherenceProperty,addCoherencePoint,addCoherencePremise,
    addResult_rew,orderIso_rew,Ordinal.domain_rew,Ordinal.zero_rew,Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def additionCoherenceApply {Γ : List Form} (x y b c r s : Nat)
    (h : ND.Proof Γ addCoherenceStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hc : ND.Proof Γ (Ordinal.domain (.fvar c)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (addResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 addCoherence (.fvar x)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      ((try simp only [addCoherenceStatement]) <;> coherenceInductionSyntax)
  exact mp (andIntro hy (andIntro hb (andIntro hc
    (andIntro hxy (andIntro hbc (andIntro hr hs))))))
    (addCoherenceAt x y b c r s (mp hx hh))

#print axioms additionCoherenceApply
end M6.PA.RelationalSource.PairGraph
