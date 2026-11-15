import PA194Transfer42Model
import PA194SourceFetchModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194Transfer42Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194SourceFetchModel PA194Transfer42Loop PA194Transfer42Invariant PA194Transfer42Model
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

theorem transferComplete (args : Fin 11 → M) (tail : M) :
    let n := args 7
    let out := PA194Transfer42Invariant.argsAt args n
    F PA194SourceControllerCode.run ![PA194Transfer42Invariant.three n+1,sourceState 42 args tail] = sourceState 45 out tail ∧
    out 7 = 0 ∧ out 8 = args 8+args 7 ∧
    ∀ i : Fin 11, i ≠ 7 → i ≠ 8 → out i = args i := by
  let n := args 7
  let out := PA194Transfer42Invariant.argsAt args n
  have hz : out 7 = (0 : M) := by simp [out,n,PA194Transfer42Invariant.argsAt,subSelf]
  have hrun := PA194Transfer42Model.runDrain args tail n (le_refl n)
  rw [PA194Transfer42Invariant.frameCorrect] at hrun
  change F PA194SourceControllerCode.run ![PA194Transfer42Invariant.three n,sourceState 42 args tail] = sourceState 42 out tail at hrun
  have hexit := transferExit out tail hz
  refine ⟨?_,hz,?_,?_⟩
  · change F (iterate PA194SourceControllerCode.step) ![PA194Transfer42Invariant.three n+1,sourceState 42 args tail] = _
    rw [iterateSucc]
    change F PA194SourceControllerCode.step ![F PA194SourceControllerCode.run ![PA194Transfer42Invariant.three n,sourceState 42 args tail]] = _
    rw [hrun,hexit]
  · simp [out,n,PA194Transfer42Invariant.argsAt]
  · intro i h7 h8
    simp [out,PA194Transfer42Invariant.argsAt,Function.update_of_ne h7,Function.update_of_ne h8]
#print axioms transferComplete
end models
end PA194Transfer42Complete
