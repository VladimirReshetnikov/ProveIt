import PA194AX11HSourceAt
import PA194PausedReach
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194AX11HMPDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SchedulerFetchPositive PA194SourceRegisterRelation
open PA194SourceFetchLoop PA194AX11HSourceAt

theorem row48 : PA194AX11HSource.program[48]'(by rw [PA194AX11HSource.program_length]; decide) =
    some (.dec 3 (some 3660) (some 49)) := by decide +kernel
theorem row49 : PA194AX11HSource.program[49]'(by rw [PA194AX11HSource.program_length]; decide) =
    some (.dec 3 (some 3572) (some 50)) := by decide +kernel
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
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 48 a tail)
      (sourceState 3572 (Function.update a 3 0) tail) := by
  let b := Function.update a 3 0
  have h48 := PA194AX11HSourceAt.sourceDecPositive 48 49 3 (some 3660) (by decide) row48 a tail 0 (by simpa [regsOfArgs] using opcode)
  have h49 := PA194AX11HSourceAt.sourceDecZero 49 3572 3 (some 50) (by decide) row49 b tail (by simp [regsOfArgs,b])
  exact PA194PausedReach.append _ (PA194PausedReach.oneStep _ h48) (PA194PausedReach.oneStep _ h49)
#print axioms row48
#print axioms row49
#print axioms mp
end models
end PA194AX11HMPDispatch
