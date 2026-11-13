module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightSuccessorOutputRight
@[expose] public section

/-! Capture-safe elimination of the first real predecessor output. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addRightSuccessorOutputs {Γ : List Form} (p x b c r s v : Nat)
    (I : AdditionRightSuccessorOutputFrame Γ p x b c r s v) :
    ND.Proof Γ (orderIso (.fvar v) (.fvar s)) := by
  have prev := addResultPredecessor I.step.basis.equality p x b r I.step.basis.separation
    I.step.domain I.step.successor I.leftResult
  apply exsElim prev
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (addResult (.fvar p) (.fvar b) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar r))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (addResult (.fvar (p+1)) (.fvar (b+1)) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (.fvar (r+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> addRightSuccessorSyntax)
  let J := I.shift.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have out := addRightSuccessorOutputRight (p+1) (x+1) (b+1) (c+1) (r+1) (s+1) (v+1) 0 J
    (andLeft hd) (andLeft (andRight hd)) (andRight (andRight hd))
  convert out using 1 <;> (dsimp [C,body] <;> addRightSuccessorSyntax)

#print axioms addRightSuccessorOutputs
end M6.PA.RelationalSource.PairGraph
