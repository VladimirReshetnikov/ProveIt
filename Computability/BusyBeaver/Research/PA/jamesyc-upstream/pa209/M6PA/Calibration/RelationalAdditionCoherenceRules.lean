module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceSyntax
public import M6PA.Calibration.RelationalAdditionRewriting
public import M6PA.Calibration.PAForwardRelationalRewriting
@[expose] public section

/-! Capture-aware specialization of the universally quantified coherence IH. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

theorem coherenceRewNeg {n m : Nat} (ω : Rew language Nat n Nat m)
    (p : Ordinal.Formula n) :
    Semiformula.rewAux ω p.neg = (Semiformula.rewAux ω p).neg := Semiformula.rewAux_neg ω p

macro "addCoherenceSyntax" : tactic => `(tactic|
  (simp only [addCoherence,addCoherenceProperty,addCoherencePoint,addCoherencePremise,
    addResult_rew,orderIso_rew,Ordinal.domain_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def addCoherenceAt {Γ : List Form} (x y b c r s : Nat)
    (h : ND.Proof Γ (addCoherence (.fvar x))) :
    ND.Proof Γ (addCoherencePoint (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  have out := allElim _ (.fvar s) (allElim _ (.fvar r)
    (allElim _ (.fvar c) (allElim _ (.fvar b) (allElim _ (.fvar y) h))))
  convert out using 1 <;> addCoherenceSyntax

def addCoherenceShift {Γ : List Form} (x : Nat)
    (h : ND.Proof Γ (addCoherence (.fvar x))) :
    ND.Proof (shifted Γ) (addCoherence (.fvar (x+1))) := by
  convert shiftProof h using 1 <;> addCoherenceSyntax

#print axioms addCoherenceAt
#print axioms addCoherenceShift
end M6.PA.RelationalSource.PairGraph
