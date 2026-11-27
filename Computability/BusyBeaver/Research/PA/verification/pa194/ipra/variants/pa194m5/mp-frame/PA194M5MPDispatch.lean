import PA194ProgramDrain
import PA194M5Program
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5MPDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194ProgramDrain PA194M5Program

theorem row48 : row program 48 =
    some (.dec 3 (some 3722) (some 49)) := by decide +kernel
theorem row49 : row program 49 =
    some (.dec 3 (some 3614) (some 50)) := by decide +kernel
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

theorem mp (a : Fin 11 → M) (tail : M) (opcode : a 3 = 1) :
    PA194ProgramDrain.Reaches program (sourceState 48 a tail)
      (sourceState 3614 (Function.update a 3 0) tail) := by
  let b := Function.update a 3 0
  have h48 := PA194ProgramDrain.sourceDecPositive program 48 49 3 (some 3722) (by rw [programLength]; decide) row48 a tail 0 (by simpa [regsOfArgs] using opcode)
  have h49 := PA194ProgramDrain.sourceDecZero program 49 3614 3 (some 50) (by rw [programLength]; decide) row49 b tail (by simp [regsOfArgs,b])
  exact PA194ProgramDrain.append program (PA194ProgramDrain.oneStep program h48).reaches (PA194ProgramDrain.oneStep program h49).reaches
#print axioms row48
#print axioms row49
#print axioms mp
end models
end PA194M5MPDispatch
