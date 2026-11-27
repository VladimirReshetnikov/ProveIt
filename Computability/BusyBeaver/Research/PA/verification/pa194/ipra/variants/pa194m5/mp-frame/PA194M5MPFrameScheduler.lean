import PA194M5MPFrame
import PA194M5GenericMPScheduler
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194M5MPFrameScheduler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion PRASubAddition TableDispatch
open PA194SchedulerCode PA194SchedulerIteration PA194MachineProjections
open PA194SchedulerSourceFrame PA194IteratedSimulation
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
theorem advance (s : M) (hMP : F (head fN fL) ![s] = 1) (axL axT axW axD axH : Code 1) :
    ∃ n : M, 0 < n ∧
      F (iterate (PA194ProgramDrain.step PA194M5Program.program)) ![n,F frame ![s]] =
      F frame ![F (PA194M5GenericMPScheduler.stepAlt axL axT axW axD axH) ![s]] := by
  obtain ⟨hn,hl,ht,hw,hd,hh⟩ := PA194M5GenericMPScheduler.nextFields s hMP axL axT axW axD axH
  exact PA194M5MPFrame.advance s _ hMP hn hl ht hw hd hh
#print axioms advance
end models
end PA194M5MPFrameScheduler
