module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedVariableEqualityTransport
@[expose] public section

/-! Real variable-value witnesses have the declared representatives as their
ordinary-equality endpoints; no uniqueness of arbitrary term values is assumed. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def boundVariablePayloadIso {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (x : Term 0)
    (h : ND.Proof Γ (equalityPayload (.bvar i) (.bvar j) b f x)) :
    ND.Proof Γ (PairGraph.orderIso (b i) (b j)) := by
  apply exsElim h
  let body : Formula 1 := value (.bvar i) (shiftEnv b) (shiftEnv f) (Rew.bShift x) ⋏
    (value (.bvar j) (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏ PairGraph.orderIso (Rew.bShift x) (.bvar 0))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun k => Rew.shift (b k)
  let fs : Nat → Term 0 := fun k => Rew.shift (f k)
  have hd : ND.Proof C (value (.bvar i) bs fs (Rew.shift x) ⋏
      (value (.bvar j) bs fs (.fvar 0) ⋏ PairGraph.orderIso (Rew.shift x) (.fvar 0))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body,bs,fs] <;> interpretedWitnessSyntax <;> (try (simp only [ND.eq,eqAtom]; interpretedWitnessSyntax)))
  have hl := andLeft hd
  have hr := andLeft (andRight hd)
  rw [value_bvar] at hl hr
  have out := interpretedIsoTransport
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp))
    (Rew.shift x) (bs i) (.fvar 0) (bs j) (andRight hl) (andRight hr) (andRight (andRight hd))
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax <;> (try (simp only [ND.eq,eqAtom]; interpretedWitnessSyntax)))

#print axioms boundVariablePayloadIso
end M6.PA.ForwardRelational
