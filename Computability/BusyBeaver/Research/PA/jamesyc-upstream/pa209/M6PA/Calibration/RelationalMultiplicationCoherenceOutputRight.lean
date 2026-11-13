module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceFrame
public import M6PA.Calibration.RelationalMultiplicationRestrictionResult
@[expose] public section

/-! Eliminate the actual right predecessor-output witness before lifting the IH. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] mulResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

macro "mulCoherenceWitnessSyntax" : tactic => `(tactic|
  (simp only [mulPredecessorResult,mulResult_rew,addResult_rew,orderIso_rew,Ordinal.domain_rew,
    Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def mulCoherencePreviousShift {Γ : List Form} (p b r : Nat)
    (h : ND.Proof Γ (mulPredecessorResult (.fvar p) (.fvar b) (.fvar r))) :
    ND.Proof (shifted Γ) (mulPredecessorResult (.fvar (p+1)) (.fvar (b+1)) (.fvar (r+1))) := by
  convert shiftProof h using 1 <;> mulCoherenceWitnessSyntax

def multiplicationCoherenceOutputRight {Γ : List Form} (p q b c r s v : Nat)
    (I : MultiplicationCoherenceFrame Γ p q b c)
    (hv : ND.Proof Γ (Ordinal.domain (.fvar v)))
    (hp : ND.Proof Γ (mulResult (.fvar p) (.fvar b) (.fvar v)))
    (hr : ND.Proof Γ (addResult (.fvar v) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulPredecessorResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  apply exsElim hs
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (mulResult (.fvar q) (.fvar c) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar c) (.fvar s))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (mulResult (.fvar (q+1)) (.fvar (c+1)) (.fvar 0) ⋏
        addResult (.fvar 0) (.fvar (c+1)) (.fvar (s+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> mulCoherenceWitnessSyntax)
  let J := I.shift.weaken (fun t ht => List.mem_cons_of_mem body.free ht)
  have iso := multiplicationCoherenceUse (p+1) (q+1) (b+1) (c+1) (v+1) 0 J
    (up (mulCoherenceResultShift p b v hp) body.free) (andLeft (andRight hd))
  have out := additionCoherenceApply (v+1) 0 (b+1) (c+1) (r+1) (s+1) J.addition
    (up (Ordinal.domainShift v hv) body.free) (andLeft hd) J.leftBaseDomain J.rightBaseDomain
    iso J.baseIso (up (coherenceResultShift v b r hr) body.free) (andRight (andRight hd))
  convert out using 1 <;> (dsimp [C,body] <;> mulCoherenceWitnessSyntax)

#print axioms mulCoherencePreviousShift
#print axioms multiplicationCoherenceOutputRight
end M6.PA.RelationalSource.PairGraph
