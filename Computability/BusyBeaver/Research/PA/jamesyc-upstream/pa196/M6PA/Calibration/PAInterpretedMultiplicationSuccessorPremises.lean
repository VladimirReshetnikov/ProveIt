module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedMultiplicationSuccessorValues
public import M6PA.Calibration.PAInterpretedAdditionSuccessorPremises
public import M6PA.Calibration.PAInterpretedEqualityTransitivity
public import M6PA.Calibration.RelationalMultiplicationPARecursion
@[expose] public section

/-! Multiplication's literal PA orientation uses the proved commutativity bridge
and closed order-isomorphism composition in addition to the paid arithmetic inputs. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

structure MultiplicationImagePremises (Γ : List Form) where
  additionImage : AdditionImagePremises Γ
  commutativity : ND.Proof Γ PairGraph.addCommutativityStatement
  transitivity : ND.Proof Γ PairGraph.isoTransitivityClosed

def MultiplicationImagePremises.up {Γ : List Form} (I : MultiplicationImagePremises Γ) (p : Form) :
    MultiplicationImagePremises (p::Γ) :=
  ⟨I.additionImage.up p,ND.up I.commutativity p,ND.up I.transitivity p⟩

def MultiplicationImagePremises.shift {Γ : List Form} (I : MultiplicationImagePremises Γ) :
    MultiplicationImagePremises (shifted Γ) :=
  ⟨I.additionImage.shift,PairGraph.additionCommutativityClosedShift I.commutativity,
    interpretedTransitivityShift I.transitivity⟩

attribute [local irreducible] PairGraph.addResult PairGraph.mulResult PairGraph.orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def multiplicationImageRightWitness {Γ : List Form} (I : MultiplicationImagePremises Γ)
    (T : TotalityPremises Γ) (x b u l r : Nat)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x))) (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (Ordinal.domain (.fvar r)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar x) (.fvar u)))
    (hl : ND.Proof Γ (PairGraph.mulResult (.fvar u) (.fvar b) (.fvar l)))
    (h : ND.Proof Γ (multiplicationSuccessorRight (.fvar x) (.fvar b) (.fvar r))) :
    ND.Proof Γ (PairGraph.orderIso (.fvar l) (.fvar r)) := by
  apply exsElim h
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (PairGraph.mulResult (.fvar x) (.fvar b) (.bvar 0) ⋏ PairGraph.addResult (.fvar b) (.bvar 0) (.fvar r))
  let C := body.free::shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (PairGraph.mulResult (.fvar (x+1)) (.fvar (b+1)) (.fvar 0) ⋏
        PairGraph.addResult (.fvar (b+1)) (.fvar 0) (.fvar (r+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> multiplicationValuePayloadSyntax)
  let J := I.shift.up body.free
  let TT := T.shift.up body.free
  have db := up (Ordinal.domainShift b hb) body.free
  have dr := up (Ordinal.domainShift r hr) body.free
  have output := TT.addAt (.fvar 0) (.fvar (b+1)) (andLeft hd) db
  have rev := PairGraph.multiplicationPARecursion J.additionImage.coherence.equality
    (x+1) (u+1) (b+1) 0 (r+1) (l+1)
    J.additionImage.separation J.additionImage.identity J.additionImage.coherence.addition
    J.additionImage.coherence.multiplication J.commutativity J.transitivity
    (up (Ordinal.domainShift x hx) body.free) db (andLeft hd) dr
    (up (Ordinal.successorShift x u hs) body.free) (andLeft (andRight hd)) (andRight (andRight hd))
    (up (PairGraph.mulCoherenceResultShift u b l hl) body.free) output
  have out := PairGraph.isoSymmetryClosedAt (r+1) (l+1) J.additionImage.symmetry dr rev
  convert out using 1 <;> (dsimp [C,body] <;> interpretedWitnessSyntax)

#print axioms MultiplicationImagePremises.shift
#print axioms multiplicationImageRightWitness
end M6.PA.ForwardRelational
