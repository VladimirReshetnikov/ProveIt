module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedVariableEqualityPayload
@[expose] public section

/-! Exact variable-equality elimination to actual order isomorphism. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

theorem freeDoubleShift (x : Term 0) :
    Rew.free (Rew.bShift (Rew.bShift x)) = Rew.bShift (Rew.shift x) := by
  cases x with
  | bvar i => nomatch i
  | func fn _ => nomatch fn
  | fvar k => rfl

def boundVariableEqualityIso {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (h : ND.Proof Γ (equal (.bvar i) (.bvar j) b f)) :
    ND.Proof Γ (PairGraph.orderIso (b i) (b j)) := by
  apply exsElim h
  let body : Formula 1 := ∃¹ (value (.bvar i) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
    (value (.bvar j) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
      PairGraph.orderIso (.bvar 1) (.bvar 0)))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun k => Rew.shift (b k)
  let fs : Nat → Term 0 := fun k => Rew.shift (f k)
  have hd : ND.Proof C (equalityPayload (.bvar i) (.bvar j) bs fs (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;>
      (dsimp [body,bs,fs] <;> (try simp only [equalityPayload]) <;> interpretedWitnessSyntax <;> (simp only [ND.eq,eqAtom]; interpretedWitnessSyntax <;> simp only [freeDoubleShift] <;> (try constructor) <;> first | rfl | trivial))
  have out := boundVariablePayloadIso
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)) i j bs fs (.fvar 0) hd
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax <;> (simp only [ND.eq,eqAtom]; interpretedWitnessSyntax <;> simp only [freeDoubleShift] <;> (try constructor) <;> first | rfl | trivial))

#print axioms boundVariableEqualityIso
end M6.PA.ForwardRelational

