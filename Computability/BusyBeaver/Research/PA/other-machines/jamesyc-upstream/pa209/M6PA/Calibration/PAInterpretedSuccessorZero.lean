module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualitySymmetry
public import M6PA.Calibration.RelationalOrderIsoSuccessorZero
@[expose] public section

/-! A genuine successor term-value cannot be a raw empty representative. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain Ordinal.zero Ordinal.successor
set_option maxHeartbeats 800000

def successorValueZeroFalse {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) (u : Nat)
    (hv : ND.Proof Γ (value (Presentation.succ t) b f (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar u))) : ND.Proof Γ ⊥ := by
  rw [value_succ] at hv
  apply exsElim (andRight hv)
  let body : Formula 1 := value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏
    Ordinal.successor (.bvar 0) (.fvar u)
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (value t bs fs (.fvar 0) ⋏ Ordinal.successor (.fvar 0) (.fvar (u+1))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body,bs,fs] <;> interpretedWitnessSyntax)
  have out := PairGraph.noSuccessorZero
    (E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)) 0 (u+1)
    (up (Ordinal.zeroShift u hz) body.free) (andRight hd)
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms successorValueZeroFalse
end M6.PA.ForwardRelational
