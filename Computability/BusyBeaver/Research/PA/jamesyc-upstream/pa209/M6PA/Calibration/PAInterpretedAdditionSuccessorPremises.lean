module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedAdditionSuccessorValues
public import M6PA.Calibration.PAInterpretedEqualitySymmetryRight
public import M6PA.Calibration.RelationalAdditionSuccessorLaw
public import M6PA.Calibration.RelationalAdditionRightSuccessor
@[expose] public section

/-! Explicit paid inputs for the literal addition-successor image. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

structure AdditionImagePremises (Γ : List Form) where
  coherence : CoherencePremises Γ
  identity : ND.Proof Γ PairGraph.identityStatement
  separation : ND.Proof Γ PairGraph.closedInclusiveSeparation
  symmetry : ND.Proof Γ PairGraph.isoSymmetryClosed

def AdditionImagePremises.up {Γ : List Form} (I : AdditionImagePremises Γ) (p : Form) :
    AdditionImagePremises (p::Γ) :=
  ⟨I.coherence.up p,ND.up I.identity p,ND.up I.separation p,ND.up I.symmetry p⟩

def AdditionImagePremises.shift {Γ : List Form} (I : AdditionImagePremises Γ) :
    AdditionImagePremises (shifted Γ) :=
  ⟨I.coherence.shift,PairGraph.rightSuccessorIdentityShift I.identity,
    PairGraph.additionInclusiveSeparationShift I.separation,interpretedSymmetryShift I.symmetry⟩

attribute [local irreducible] PairGraph.addResult PairGraph.orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def additionImageRightWitness {Γ : List Form} (I : AdditionImagePremises Γ)
    (x b u l r : Nat) (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (Ordinal.domain (.fvar r)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar x) (.fvar u)))
    (hl : ND.Proof Γ (PairGraph.addResult (.fvar u) (.fvar b) (.fvar l)))
    (h : ND.Proof Γ (additionSuccessorRight (.fvar x) (.fvar b) (.fvar r))) :
    ND.Proof Γ (PairGraph.orderIso (.fvar l) (.fvar r)) := by
  apply exsElim h
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (PairGraph.addResult (.fvar x) (.fvar b) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar r))
  let C := body.free::shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (PairGraph.addResult (.fvar (x+1)) (.fvar (b+1)) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (.fvar (r+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> additionValuePayloadSyntax)
  let J := I.shift.up body.free
  have rev := PairGraph.additionSuccessorLaw J.coherence.equality (x+1) (u+1) (b+1) 0 (r+1) (l+1)
    J.coherence.empty J.coherence.adjunction J.separation J.identity J.coherence.addition
    (up (Ordinal.domainShift x hx) body.free) (up (Ordinal.domainShift b hb) body.free) (andLeft hd)
    (up (Ordinal.successorShift x u hs) body.free) (andRight (andRight hd)) (andLeft (andRight hd))
    (up (PairGraph.coherenceResultShift u b l hl) body.free)
  have out := PairGraph.isoSymmetryClosedAt (r+1) (l+1) J.symmetry
    (up (Ordinal.domainShift r hr) body.free) rev
  convert out using 1 <;> (dsimp [C,body] <;> interpretedWitnessSyntax)

#print axioms AdditionImagePremises.shift
#print axioms additionImageRightWitness
end M6.PA.ForwardRelational
