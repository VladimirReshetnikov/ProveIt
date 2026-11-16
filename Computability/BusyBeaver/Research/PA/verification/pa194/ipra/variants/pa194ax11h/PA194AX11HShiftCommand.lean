import PA194AX11HCacheInput
import PA194AX11HShiftGuard
import PA194AX11HShiftReader

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194AX11HShiftCommand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode (pc)
open PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194MachineProjections
open PA194IteratedSimulation

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def output (a : Fin 11 → M) : Fin 11 → M :=
  Function.update (Function.update (Function.update
    (Function.update (Function.update a 1 (a 5)) 2 (F fixedSecond ![a 2]))
    5 (F fixedFirst ![a 2])) 6 0) 7 0

/-- A nonhalting SHIFT clears the old cache and unpacks the stack. -/
theorem decoded (a : Fin 11 → M) (tail : M) (opcode : a 3 = 0) (cache : a 5 ≠ 1)
    (scratch : a 6 = 0) (scratch' : a 7 = 0) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 48 a tail)
      (sourceState 25 (output a) tail) := by
  let ready := Function.update a 1 (a 5)
  let cleared := Function.update ready 5 (0 : M)
  have enter := PA194AX11HCacheInput.prepare a tail opcode scratch
  have guard := PA194AX11HShiftGuard.guardReturns ready tail
    (by simpa [ready] using scratch) (by simpa [ready] using cache)
  have reader := PA194AX11HShiftReader.execute cleared tail
    (by simpa [cleared,ready] using scratch) (by simpa [cleared,ready] using scratch')
  let result := Function.update (Function.update
    (Function.update (Function.update cleared 2 (F fixedSecond ![cleared 2]))
      5 (cleared 5 + F fixedFirst ![cleared 2])) 6 0) 7 0
  have hr : result = output a := by
    funext i
    fin_cases i <;> simp [result,output,cleared,ready]
  change PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 11 cleared tail)
    (sourceState 25 result tail) at reader
  rw [hr] at reader
  have path := PA194PausedReach.append PA194AX11HSource.step guard reader
  exact PA194PausedReach.append PA194AX11HSource.step enter path

#print axioms decoded
end models
end PA194AX11HShiftCommand
