module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedAdditionSuccessorEquality
public import M6PA.Calibration.PAInterpretedFunctionCongruenceGuards
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! Exact literal typed PAeq addition-successor image. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def interpretedAddSucc {Γ : List Form} (I : AdditionImagePremises Γ)
    (T : TotalityPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.addSucc Fin.elim0 f) := by
  apply interpretedAllIntro
  apply interpretedAllIntro
  let d : Form := Ordinal.domain (.fvar 0)
  let fs : Nat → Term 0 := fun i => Rew.shift (Rew.shift (f i))
  have out := additionSuccessorVariablesEqual ((I.shift.up d).shift.up d)
    (functionGuardTotality T 2) 0 1 (functionBoundEnv 2) fs
    (functionGuardDomain 2 0) (functionGuardDomain 2 1)
  convert out using 1 <;>
    (dsimp [d,fs,functionBoundEnv,functionGuardContext,freeShiftEnv] <;>
      (try simp only [formula,Presentation.eq]) <;> rfl)

#print axioms interpretedAddSucc
end M6.PA.ForwardRelational
