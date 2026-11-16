module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedZeroSuccessorPayload
@[expose] public section

/-! No arbitrary source successor term is interpreted as equal to zero. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain Ordinal.zero Ordinal.successor
set_option maxHeartbeats 800000

def zeroSuccessorEqualityFalse {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (h : ND.Proof Γ (equal Presentation.zero (Presentation.succ t) b f)) : ND.Proof Γ ⊥ := by
  apply exsElim h
  let body : Formula 1 := ∃¹ (value Presentation.zero (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
    (value (Presentation.succ t) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
      PairGraph.orderIso (.bvar 1) (.bvar 0)))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (equalityPayload Presentation.zero (Presentation.succ t) bs fs (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;>
      (dsimp [body,bs,fs] <;> (try simp only [equalityPayload]) <;> interpretedWitnessSyntax)
  have out := zeroSuccessorPayloadFalse
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)) t bs fs 0 hd
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

def zeroSuccessorEqualityNeg {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) :
    ND.Proof Γ (equal Presentation.zero (Presentation.succ t) b f).neg := by
  apply byContradiction
  let p : Form := (equal Presentation.zero (Presentation.succ t) b f).neg.neg
  have h : ND.Proof (p::Γ) (equal Presentation.zero (Presentation.succ t) b f) :=
    assumption (by simp [p,Semiformula.neg_neg])
  exact zeroSuccessorEqualityFalse (E.weaken (fun q hq => List.mem_cons_of_mem p hq)) t b f h

#print axioms zeroSuccessorEqualityFalse
#print axioms zeroSuccessorEqualityNeg
end M6.PA.ForwardRelational

