module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightSuccessorOutputs
@[expose] public section

/-! The fully parameterized step of right-successor induction. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addRightSuccessorStepPoint {Γ : List Form} (p x b c r s v : Nat)
    (I : AdditionRightSuccessorStepFrame Γ p x) :
    ND.Proof Γ (addRightSuccessorPoint (.fvar x) (.fvar b) (.fvar c) (.fvar r) (.fvar s) (.fvar v)) := by
  apply impIntro
  let d : Form := addRightSuccessorPremise (.fvar x) (.fvar b) (.fvar c) (.fvar r) (.fvar s) (.fvar v)
  have hd : ND.Proof (d::Γ) d := assumption (by simp)
  have h1 := andRight (andRight (andRight hd))
  let J : AdditionRightSuccessorOutputFrame (d::Γ) p x b c r s v :=
    ⟨I.weaken (fun q hq => List.mem_cons_of_mem d hq),andLeft hd,andLeft (andRight hd),
      andLeft (andRight (andRight hd)),andLeft h1,andLeft (andRight h1),
      andLeft (andRight (andRight h1)),andRight (andRight (andRight h1))⟩
  exact addRightSuccessorOutputs p x b c r s v J

def addRightSuccessorStep {Γ : List Form} (p x : Nat)
    (I : AdditionRightSuccessorStepFrame Γ p x) :
    ND.Proof Γ (addRightSuccessor (.fvar x)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  have out := addRightSuccessorStepPoint (p+1+1+1+1+1) (x+1+1+1+1+1) 4 3 2 1 0
    I.shift.shift.shift.shift.shift
  convert out using 1 <;> addRightSuccessorSyntax

#print axioms addRightSuccessorStepPoint
#print axioms addRightSuccessorStep
end M6.PA.RelationalSource.PairGraph
