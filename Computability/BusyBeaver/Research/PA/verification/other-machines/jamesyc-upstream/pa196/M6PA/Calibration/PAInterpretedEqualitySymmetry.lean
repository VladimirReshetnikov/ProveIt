module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualitySymmetryRight
@[expose] public section

/-! Symmetry of interpreted equality for arbitrary source terms and finite
binder arities, retaining both real value witnesses. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 600000

def equalitySymmetry {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (hsym : ND.Proof Γ PairGraph.isoSymmetryClosed)
    (h : ND.Proof Γ (equal s t b f)) : ND.Proof Γ (equal t s b f) := by
  apply exsElim h
  let body : Formula 1 := ∃¹ (value s (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
    (value t (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏ PairGraph.orderIso (.bvar 1) (.bvar 0)))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (equalityPayload s t bs fs (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;>
      (dsimp [body,bs,fs] <;> (try simp only [equalityPayload]) <;> interpretedWitnessSyntax)
  have out := equalitySymmetryRight s t bs fs (.fvar 0)
    (up (interpretedSymmetryShift hsym) body.free) hd
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms equalitySymmetry
end M6.PA.ForwardRelational

