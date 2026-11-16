import PA194Transfer42OpenComplete
import PA194Transfer45OpenComplete
import PA194IterateAddOpen
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DispatchTransfersOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194IterateAddOpen PA194UnpairDrainOpenComplete
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem transferToDispatch (args : Fin 11 → M) (tail : M) :
    let mid := PA194Transfer42Open.argsAt args (args 7)
    let out := PA194Transfer45Open.argsAt mid (mid 6)
    let clock := (PA194Transfer42Open.three (args 7)+1)+(PA194Transfer45Open.three (args 6)+1)
    F PA194SourceControllerCode.run ![clock,sourceState 42 args tail] = sourceState 48 out tail ∧
    out 3 = args 3+args 6 ∧ out 8 = args 8+args 7 ∧ out 6 = 0 ∧ out 7 = 0 ∧
    ∀ i : Fin 11, i ≠ 3 → i ≠ 6 → i ≠ 7 → i ≠ 8 → out i = args i := by
  let mid := PA194Transfer42Open.argsAt args (args 7)
  let out := PA194Transfer45Open.argsAt mid (mid 6)
  let c1 := PA194Transfer42Open.three (args 7)+1
  let c2 := PA194Transfer45Open.three (args 6)+1
  have hm6 : mid 6 = args 6 := by simp [mid,PA194Transfer42Open.argsAt]
  have h42 := PA194Transfer42OpenComplete.transferComplete args tail
  change F PA194SourceControllerCode.run ![c1,sourceState 42 args tail] = sourceState 45 mid tail ∧ _ at h42
  have h45 := PA194Transfer45OpenComplete.transferComplete mid tail
  change F PA194SourceControllerCode.run ![PA194Transfer45Open.three (mid 6)+1,sourceState 45 mid tail] = sourceState 48 out tail ∧ _ at h45
  rw [hm6] at h45
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · change F (iterate PA194SourceControllerCode.step) ![c1+c2,sourceState 42 args tail] = _
    rw [PA194IterateAddOpen.iterateAdd]
    change F PA194SourceControllerCode.run ![c2,F PA194SourceControllerCode.run ![c1,sourceState 42 args tail]] = _
    rw [h42.1]
    exact h45.1
  · simp [out,mid,PA194Transfer45Open.argsAt,PA194Transfer42Open.argsAt]
  · simp [out,mid,PA194Transfer45Open.argsAt,PA194Transfer42Open.argsAt]
  · simp [out,mid,PA194Transfer45Open.argsAt,PA194Transfer42Open.argsAt,subSelf]
  · simp [out,mid,PA194Transfer45Open.argsAt,PA194Transfer42Open.argsAt,subSelf]
  · intro i h3 h6 h7 h8
    simp [out,mid,PA194Transfer45Open.argsAt,PA194Transfer42Open.argsAt,Function.update_of_ne h3,Function.update_of_ne h6,Function.update_of_ne h7,Function.update_of_ne h8]
#print axioms transferToDispatch
end models
end PA194DispatchTransfersOpen
