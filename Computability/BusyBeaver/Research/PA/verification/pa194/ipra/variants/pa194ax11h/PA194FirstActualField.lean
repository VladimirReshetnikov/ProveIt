import PA194PausedTransfer
import PA194PausedReader
import PA194PausedFirstHit
import PA194ModelMPField

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194FirstActualField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194ModelMPDrain
open PA194MachineProjections PA194TargetCantor PA194ModelMPField
open PA194PausedSites PA194PausedTransfer PA194IteratedSimulation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The original field reader reaches the exact decoded state under its
transition code frozen at site 3568. -/
theorem paused_field (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    PA194PausedReach.Reaches PA194AX11HFieldPaused.oldPaused
      (sourceState 3554 a tail) (sourceState 3568 (fieldArgs a) tail) := by
  have h := PA194PausedReader.reader PA194AX11HFieldPaused.oldPaused 3568 3554
    field_agrees (by decide) 8 4 fieldRows a tail
  dsimp only at h
  have hz : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hX,hY,hz,zero_add] at h
  let x := F fixedFirst ![a 8]
  let y := F fixedSecond ![a 8]
  have ho := PA194AXReaderAlgebra.outputD a x y
  dsimp only at ho
  change PA194PausedReach.Reaches PA194AX11HFieldPaused.oldPaused _ (sourceState 3568
    (argsAfter (argsAfter (PA194AXReaderAlgebra.decoded a x y) 7 [8]
      (PA194AXReaderAlgebra.decoded a x y 7)) 6 [4]
      ((argsAfter (PA194AXReaderAlgebra.decoded a x y) 7 [8]
      (PA194AXReaderAlgebra.decoded a x y 7)) 6)) tail) at h
  rw [ho] at h
  have hs : Function.update (Function.update (fieldArgs a) 6 0) 7 0 = fieldArgs a := by
    funext i
    fin_cases i <;> simp [fieldArgs,hX,hY]
  exact hs ▸ h

/-- The first actual primary exit of the field reader has the exact decoded file. -/
theorem first_actual_field (a : Fin 11 → M) (tail : M) (hX : a 6 = 0) (hY : a 7 = 0) :
    ∃ n : M, F (iterate step) ![n,sourceState 3554 a tail] = sourceState 3568 (fieldArgs a) tail ∧
      ∀ j < n, F pc ![F (iterate step) ![j,sourceState 3554 a tail]] ≠ modelNumeral M 3568 := by
  apply PA194PausedFirstHit.first_actual_exit PA194AX11HFieldPaused.oldPaused 3568
  · exact PA194AX11HFieldPaused.oldPaused_model
  · exact source_pc 3568 (fieldArgs a) tail
  · exact paused_field a tail hX hY

#print axioms paused_field
#print axioms first_actual_field
end models
end PA194FirstActualField
