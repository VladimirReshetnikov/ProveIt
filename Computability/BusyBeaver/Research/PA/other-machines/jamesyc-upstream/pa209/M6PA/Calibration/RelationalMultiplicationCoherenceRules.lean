module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceSyntax
public import M6PA.Calibration.RelationalAdditionCoherenceRules
public import M6PA.Calibration.PAForwardRelationalRewriting
public import M6PA.Calibration.RelationalSpecializeFive
@[expose] public section

/-! Capture-aware specialization of the universally quantified coherence IH. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] mulResult orderIso Ordinal.domain mulCoherencePoint mulCoherencePremise
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

macro "mulCoherenceSyntax" : tactic => `(tactic|
  (simp only [mulCoherence,mulCoherenceProperty,mulCoherencePoint,mulCoherencePremise,
    mulResult_rew,orderIso_rew,Ordinal.domain_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def mulCoherenceAt {Γ : List Form} (x y b c r s : Nat)
    (h : ND.Proof Γ (mulCoherence (.fvar x))) :
    ND.Proof Γ (mulCoherencePoint (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  have out := specializeFive _ y b c r s h
  convert out using 1 <;> mulCoherenceSyntax

def mulCoherenceShift {Γ : List Form} (x : Nat)
    (h : ND.Proof Γ (mulCoherence (.fvar x))) :
    ND.Proof (shifted Γ) (mulCoherence (.fvar (x+1))) := by
  convert shiftProof h using 1 <;> mulCoherenceSyntax

#print axioms mulCoherenceAt
#print axioms mulCoherenceShift
end M6.PA.RelationalSource.PairGraph
