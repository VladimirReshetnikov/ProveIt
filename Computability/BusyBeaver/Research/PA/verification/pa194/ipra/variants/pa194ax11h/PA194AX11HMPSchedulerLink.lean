import PA194AX11HGenericMPScheduler
import PA194ControllerSchedulerCore
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HMPSchedulerLink
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SchedulerCode PA194SchedulerIteration PA194ControllerScheduler
open PA194SourceControllerCode PA194SchedulerSourceFrame PA194IteratedSimulation
open PA194AX11HGenericMPScheduler

theorem link : stepAlt (tail4 fN fL) (.zero 1)
    (axStackA true fT (axArg fN fL) fD fH (yArg fN fL) (xArg fN fL) fW)
    (zField true fN fL) (.zero 1) = stepK .top true := by rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem advance (s : M) (hMP : F (head fN fL) ![s] = 1) :
    ∃ n : M, 0 < n ∧ F (iterate PA194AX11HSource.step) ![n,F frame ![s]] =
      F frame ![F (stepK .top true) ![s]] := by
  have h := PA194AX11HGenericMPScheduler.advance s hMP (tail4 fN fL) (.zero 1)
    (axStackA true fT (axArg fN fL) fD fH (yArg fN fL) (xArg fN fL) fW)
    (zField true fN fL) (.zero 1)
  rw [link] at h
  exact h
#print axioms link
#print axioms advance
end models
end PA194AX11HMPSchedulerLink
