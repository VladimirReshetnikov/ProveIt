module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedMultiplicationSuccessorEquality
public import M6PA.Calibration.PAInterpretedFunctionCongruenceGuards
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! Exact literal typed PAeq multiplication-successor image. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def interpretedMulSucc {Γ : List Form} (I : MultiplicationImagePremises Γ)
    (T : TotalityPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.mulSucc Fin.elim0 f) := by
  apply interpretedAllIntro
  apply interpretedAllIntro
  let d : Form := Ordinal.domain (.fvar 0)
  let fs : Nat → Term 0 := fun i => Rew.shift (Rew.shift (f i))
  have out := multiplicationSuccessorVariablesEqual ((I.shift.up d).shift.up d)
    (functionGuardTotality T 2) 1 0 (functionBoundEnv 2) fs
    (functionGuardDomain 2 1) (functionGuardDomain 2 0)
  convert out using 1 <;>
    (dsimp [d,fs,functionBoundEnv,functionGuardContext,freeShiftEnv] <;>
      (try simp only [formula,Presentation.eq]) <;> rfl)

#print axioms interpretedMulSucc
end M6.PA.ForwardRelational
