module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedSuccessorCancellationRight
@[expose] public section

/-! Eliminate the left successor's actual child witness. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def successorValuesCancel {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t u : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) (x y : Nat)
    (hsep : ND.Proof Γ PairGraph.closedStrictSeparation)
    (ht : ND.Proof Γ (value (Presentation.succ t) b f (.fvar x)))
    (hu : ND.Proof Γ (value (Presentation.succ u) b f (.fvar y)))
    (hi : ND.Proof Γ (PairGraph.orderIso (.fvar x) (.fvar y))) :
    ND.Proof Γ (equal t u b f) := by
  rw [value_succ] at ht
  apply exsElim (andRight ht)
  let body : Formula 1 := value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar x)
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (value t bs fs (.fvar 0) ⋏ Ordinal.successor (.fvar 0) (.fvar (x+1))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body,bs,fs] <;> interpretedWitnessSyntax)
  have huu : ND.Proof C (value (Presentation.succ u) bs fs (.fvar (y+1))) := by
    convert up (shiftProof hu) body.free using 1 <;> (dsimp [bs,fs] <;> interpretedWitnessSyntax)
  have out := successorValuesCancelRight
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)) t u bs fs 0 (x+1) (y+1)
    (up (PairGraph.predecessorClosedSeparationShift hsep) body.free) (andLeft hd) (andRight hd)
    huu (up (interpretedIsoShift x y hi) body.free)
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms successorValuesCancel
end M6.PA.ForwardRelational
