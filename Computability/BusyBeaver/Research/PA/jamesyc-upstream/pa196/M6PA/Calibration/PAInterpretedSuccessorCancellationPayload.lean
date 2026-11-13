module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedSuccessorCancellationValues
@[expose] public section

/-! Eliminate the actual right successor output witness of interpreted equality. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def successorPayloadCancel {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t u : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) (x : Nat)
    (hsep : ND.Proof Γ PairGraph.closedStrictSeparation)
    (h : ND.Proof Γ (equalityPayload (Presentation.succ t) (Presentation.succ u) b f (.fvar x))) :
    ND.Proof Γ (equal t u b f) := by
  apply exsElim h
  let body : Formula 1 := value (Presentation.succ t) (shiftEnv b) (shiftEnv f) (.fvar x) ⋏
    (value (Presentation.succ u) (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏ PairGraph.orderIso (.fvar x) (.bvar 0))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (value (Presentation.succ t) bs fs (.fvar (x+1)) ⋏
      (value (Presentation.succ u) bs fs (.fvar 0) ⋏ PairGraph.orderIso (.fvar (x+1)) (.fvar 0))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body,bs,fs] <;> interpretedWitnessSyntax)
  have out := successorValuesCancel
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)) t u bs fs (x+1) 0
    (up (PairGraph.predecessorClosedSeparationShift hsep) body.free)
    (andLeft hd) (andLeft (andRight hd)) (andRight (andRight hd))
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms successorPayloadCancel
end M6.PA.ForwardRelational
