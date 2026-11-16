module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedMultiplicationSuccessorPremises
@[expose] public section

/-! Both actual graph payloads yield the correctly oriented equality image. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] PairGraph.mulResult PairGraph.orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def multiplicationImagePayloads {Γ : List Form} (I : MultiplicationImagePremises Γ) (T : TotalityPremises Γ)
    (x b l r : Nat) (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (Ordinal.domain (.fvar r)))
    (hl : ND.Proof Γ (multiplicationSuccessorLeft (.fvar x) (.fvar b) (.fvar l)))
    (hrr : ND.Proof Γ (multiplicationSuccessorRight (.fvar x) (.fvar b) (.fvar r))) :
    ND.Proof Γ (PairGraph.orderIso (.fvar l) (.fvar r)) := by
  apply exsElim hl
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.fvar x) (.bvar 0) ⋏ PairGraph.mulResult (.bvar 0) (.fvar b) (.fvar l))
  let C := body.free::shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (Ordinal.successor (.fvar (x+1)) (.fvar 0) ⋏
        PairGraph.mulResult (.fvar 0) (.fvar (b+1)) (.fvar (l+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> multiplicationValuePayloadSyntax)
  have hs : ND.Proof C (multiplicationSuccessorRight (.fvar (x+1)) (.fvar (b+1)) (.fvar (r+1))) := by
    convert up (shiftProof hrr) body.free using 1 <;> multiplicationValuePayloadSyntax
  have out := multiplicationImageRightWitness (I.shift.up body.free) (T.shift.up body.free) (x+1) (b+1) 0 (l+1) (r+1)
    (up (Ordinal.domainShift x hx) body.free) (up (Ordinal.domainShift b hb) body.free)
    (up (Ordinal.domainShift r hr) body.free) (andLeft (andRight hd)) (andRight (andRight hd)) hs
  convert out using 1 <;> (dsimp [C,body] <;> interpretedWitnessSyntax)

#print axioms multiplicationImagePayloads
end M6.PA.ForwardRelational
