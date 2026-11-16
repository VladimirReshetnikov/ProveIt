import PA194DecoderRoundCode
import PA194UnpairDrainOpenComplete
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DecoderRoundOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194IteratedSimulation PA194DecoderRoundCode PA194UnpairRound
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem runFive (s : M) :
    F PA194SourceControllerCode.run ![(((((0 : M)+1)+1)+1)+1)+1,s] =
    F step ![F step ![F step ![F step ![F step ![s]]]]] := by
  change F (iterate step) ![(((((0 : M)+1)+1)+1)+1)+1,s] = _
  rw [PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterZero]

theorem advancePositive (args : Fin 11 → M) (tail w a : M)
    (hw : args 8 = w+1) (ha : args 6 = a+1) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := Function.update a2 6 a
    F advance ![sourceState 34 args tail] = sourceState 34 out tail := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := Function.update a2 6 a
  have hn : a+1 ≠ (0 : M) := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : M) ≤ a) (lt_add_one a))
  have h := positiveRound args tail w a hw ha
  change F step ![F step ![F step ![F step ![F step ![sourceState 34 args tail]]]]] = sourceState 34 out tail ∧ _ at h
  rw [advanceModel,clockModel,ha,if_neg hn,runFive]
  exact h.1

theorem advanceZero (args : Fin 11 → M) (tail w : M)
    (hw : args 8 = w+1) (hx : args 6 = (0 : M)) :
    let a1 := Function.update args 8 w
    let a2 := Function.update a1 7 (a1 7+1)
    let out := PA194UnpairDrainOpen.argsAt a2 (a2 7)
    F advance ![sourceState 34 args tail] = sourceState 34 out tail := by
  let a1 := Function.update args 8 w
  let a2 := Function.update a1 7 (a1 7+1)
  let out := PA194UnpairDrainOpen.argsAt a2 (a2 7)
  have hy : a2 7 = args 7+1 := by simp [a2,a1]
  have h := PA194UnpairDrainOpenComplete.zeroXRound args tail w hw hx
  change F PA194SourceControllerCode.run ![(((0 : M)+1)+1)+1 + ((PA194UnpairDrainOpen.three (a2 7)+1)+1),sourceState 34 args tail] = sourceState 34 out tail ∧ _ at h
  change F advance ![sourceState 34 args tail] = sourceState 34 out tail
  rw [advanceModel,clockModel,hx,if_pos rfl,←hy]
  exact h.1
#print axioms advancePositive
#print axioms advanceZero
end models
end PA194DecoderRoundOpen
