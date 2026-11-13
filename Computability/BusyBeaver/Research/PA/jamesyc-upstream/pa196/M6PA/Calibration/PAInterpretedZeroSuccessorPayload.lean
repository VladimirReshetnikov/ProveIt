module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedSuccessorZero
@[expose] public section

/-! Eliminate the right actual value witness of an alleged zero/successor equality. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain Ordinal.zero Ordinal.successor
set_option maxHeartbeats 800000

def zeroSuccessorPayloadFalse {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) (z : Nat)
    (h : ND.Proof Γ (equalityPayload Presentation.zero (Presentation.succ t) b f (.fvar z))) :
    ND.Proof Γ ⊥ := by
  apply exsElim h
  let body : Formula 1 := value Presentation.zero (shiftEnv b) (shiftEnv f) (.fvar z) ⋏
    (value (Presentation.succ t) (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏
      PairGraph.orderIso (.fvar z) (.bvar 0))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (value Presentation.zero bs fs (.fvar (z+1)) ⋏
      (value (Presentation.succ t) bs fs (.fvar 0) ⋏ PairGraph.orderIso (.fvar (z+1)) (.fvar 0))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body,bs,fs] <;> interpretedWitnessSyntax)
  have hv := andLeft hd
  rw [value_zero] at hv
  have hz := PairGraph.orderIsoZeroForward (z+1) 0 (andRight hv) (andRight (andRight hd))
  have out := successorValueZeroFalse
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)) t bs fs 0
    (andLeft (andRight hd)) hz
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms zeroSuccessorPayloadFalse
end M6.PA.ForwardRelational
