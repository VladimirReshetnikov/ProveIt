module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceFrame
public import M6PA.Calibration.RelationalAdditionRestrictionResult
@[expose] public section

/-! Eliminate the actual right predecessor-output witness before lifting the IH. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

macro "coherenceWitnessSyntax" : tactic => `(tactic|
  (simp only [addPredecessorResult,addResult_rew,orderIso_rew,Ordinal.domain_rew,
    Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def coherencePreviousShift {Γ : List Form} (p b r : Nat)
    (h : ND.Proof Γ (addPredecessorResult (.fvar p) (.fvar b) (.fvar r))) :
    ND.Proof (shifted Γ) (addPredecessorResult (.fvar (p+1)) (.fvar (b+1)) (.fvar (r+1))) := by
  convert shiftProof h using 1 <;> coherenceWitnessSyntax

def additionCoherenceOutputRight {Γ : List Form} (p q b c r s v : Nat)
    (I : AdditionCoherenceFrame Γ p q b c)
    (hv : ND.Proof Γ (Ordinal.domain (.fvar v)))
    (hp : ND.Proof Γ (addResult (.fvar p) (.fvar b) (.fvar v)))
    (hr : ND.Proof Γ (Ordinal.successor (.fvar v) (.fvar r)))
    (hs : ND.Proof Γ (addPredecessorResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  apply exsElim hs
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (addResult (.fvar q) (.fvar c) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar s))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (addResult (.fvar (q+1)) (.fvar (c+1)) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (.fvar (s+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> coherenceWitnessSyntax)
  let J := I.shift.weaken (fun t ht => List.mem_cons_of_mem body.free ht)
  have iso := additionCoherenceUse (p+1) (q+1) (b+1) (c+1) (v+1) 0 J
    (up (coherenceResultShift p b v hp) body.free) (andLeft (andRight hd))
  have out := orderIsoSuccessor J.equality (v+1) 0 (r+1) (s+1) J.empty J.adjunction
    (up (Ordinal.domainShift v hv) body.free) (andLeft hd)
    (up (Ordinal.successorShift v r hr) body.free) (andRight (andRight hd)) iso
  convert out using 1 <;> (dsimp [C,body] <;> coherenceWitnessSyntax)

#print axioms coherencePreviousShift
#print axioms additionCoherenceOutputRight
end M6.PA.RelationalSource.PairGraph
