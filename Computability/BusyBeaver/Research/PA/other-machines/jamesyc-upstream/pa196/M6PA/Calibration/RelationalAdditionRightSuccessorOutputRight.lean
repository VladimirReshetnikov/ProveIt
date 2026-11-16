module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightSuccessorFrame
@[expose] public section

/-! The second real predecessor output, and the lower right-successor IH. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addRightSuccessorOutputRight {Γ : List Form} (p x b c r s v u : Nat)
    (I : AdditionRightSuccessorOutputFrame Γ p x b c r s v)
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hl : ND.Proof Γ (addResult (.fvar p) (.fvar b) (.fvar u)))
    (hur : ND.Proof Γ (Ordinal.successor (.fvar u) (.fvar r))) :
    ND.Proof Γ (orderIso (.fvar v) (.fvar s)) := by
  have prev := addResultPredecessor I.step.basis.equality p x c s I.step.basis.separation
    I.step.domain I.step.successor I.rightResult
  apply exsElim prev
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (addResult (.fvar p) (.fvar c) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar s))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (addResult (.fvar (p+1)) (.fvar (c+1)) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (.fvar (s+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> addRightSuccessorSyntax)
  let J := I.shift.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have lower := mp (andIntro J.leftDomain (andIntro J.rightDomain
    (andIntro (up (Ordinal.domainShift u hu) body.free) (andIntro J.baseSuccessor
      (andIntro (up (coherenceResultShift p b u hl) body.free)
        (andIntro (andLeft (andRight hd)) (up (Ordinal.successorShift u r hur) body.free)))))))
    (addRightSuccessorAt (p+1) (b+1) (c+1) (u+1) 0 (r+1) J.step.hypothesis)
  have out := orderIsoSuccessor J.step.basis.equality (r+1) 0 (v+1) (s+1)
    J.step.basis.empty J.step.basis.adjunction J.outputDomain (andLeft hd)
    J.outputSuccessor (andRight (andRight hd)) lower
  convert out using 1 <;> (dsimp [C,body] <;> addRightSuccessorSyntax)

#print axioms addRightSuccessorOutputRight
end M6.PA.RelationalSource.PairGraph
