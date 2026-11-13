module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedSuccessorCancellationPayload
@[expose] public section

/-! Successor injectivity for arbitrary typed source term values. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def successorEqualityCancel {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t u : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hsep : ND.Proof Γ PairGraph.closedStrictSeparation)
    (h : ND.Proof Γ (equal (Presentation.succ t) (Presentation.succ u) b f)) :
    ND.Proof Γ (equal t u b f) := by
  apply exsElim h
  let body : Formula 1 := ∃¹
    (value (Presentation.succ t) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
    (value (Presentation.succ u) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
      PairGraph.orderIso (.bvar 1) (.bvar 0)))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (equalityPayload (Presentation.succ t) (Presentation.succ u) bs fs (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;>
      (dsimp [body,bs,fs] <;> (try simp only [equalityPayload]) <;> interpretedWitnessSyntax)
  have out := successorPayloadCancel
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)) t u bs fs 0
    (up (PairGraph.predecessorClosedSeparationShift hsep) body.free) hd
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms successorEqualityCancel
end M6.PA.ForwardRelational

