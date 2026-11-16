import PA194SeedFrameAlignment
import PA194SourceDynamicLoop
import PA194TransferMacroWidths
import Mathlib.Tactic.Abel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SeedWidthGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SeedFrameAlignment PA194ModelSourceLoop PA194ActualLoopOrbit PA194SourceSite31Physical PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem blankReachesGrowingLoop (tail : M) :
    let e : Fin 11 → M := fun i => modelNumeral M (PA194StartupSourceFrame.seedArgs i)
    let a := seedArgs30 (M := M)
    let k := modelNumeral M 39
    let count := modelNumeral M 27
    let mid := PA194Site28DynamicOutput.updated (Function.update a 0 (0 : M)) count
    let out := PA194Site29DynamicOutput.updated mid (count+1)
    let startGap := ((k+1)+1)+1
    let endGap := startGap+1
    F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![PA194SourceSite31Controller.sourceState 25 e tail]]]]] =
      PA194SourceSite31Controller.sourceState 27 a tail ∧
    ∃ c c0 c1 c2 : M,
      F PA194Stepper.stepper ![c, modelNumeral M 0] = physicalFrame 27 startGap a ∧
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
        F PA194SourceControllerCode.step ![PA194SourceSite31Controller.sourceState 27 a tail]]]] =
        PA194SourceSite31Controller.sourceState 27 out tail ∧
      F PA194Stepper.stepper ![modelNumeral M 40,F PA194Stepper.stepper ![c2,
        F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,physicalFrame 27 startGap a]]]] =
        physicalFrame 27 endGap out ∧
      PA194TransferMacroWidths.width 27 endGap = PA194TransferMacroWidths.width 27 startGap + 1 ∧
      PA194TransferMacroWidths.width 27 startGap < PA194TransferMacroWidths.width 27 endGap := by
  dsimp only
  let a := seedArgs30 (M := M)
  let k := modelNumeral M 39
  let count := modelNumeral M 27
  have hr : a 0 = (0 : M)+1 := by
    change seedRegs (M := M) 0 = (0 : M)+1
    simp [seedRegs,seedArgs30,PA194Site29OutputWithCarry.updated,PA194Site28OutputFile.updated]
  have ht : a 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)] := by
    dsimp only [a,count]
    rw [←seedFrame (M := M)]
    simp [frameArgs,PA194ActualSourceLoop.args]
  obtain ⟨hs,c,hp⟩ := PA194SeedControllerReturn27.blankAndFiveSteps (M := M) tail
  have hg : (((modelNumeral M 38+1)+1)+1)+1 = ((k+1)+1)+1 := by
    dsimp only [k]
    have hh : modelNumeral M 38 + (1 : M) = modelNumeral M 39 := by
      rw [←modelNumeralOne,←modelNumeralAdd]
    rw [hh]
  change F PA194Stepper.stepper ![c,modelNumeral M 0] =
    physicalFrame 27 ((((modelNumeral M 38+1)+1)+1)+1) a at hp
  rw [hg] at hp
  have hs' : F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![PA194SourceSite31Controller.sourceState 25
        (fun i => modelNumeral M (PA194StartupSourceFrame.seedArgs i)) tail]]]]] =
      PA194SourceSite31Controller.sourceState 27 a tail := hs
  obtain ⟨c0,c1,c2,hsLoop,hpLoop⟩ := PA194SourceDynamicLoop.fourSteps k tail count (0 : M) a hr ht
  refine ⟨hs',c,c0,c1,c2,hp,hsLoop,hpLoop,?_,?_⟩
  · simp only [PA194TransferMacroWidths.width]
    abel
  · have he : PA194TransferMacroWidths.width 27 ((((k+1)+1)+1)+1) =
        PA194TransferMacroWidths.width 27 (((k+1)+1)+1) + 1 := by
      simp only [PA194TransferMacroWidths.width]
      abel
    rw [he]
    exact lt_add_of_pos_right _ _root_.zero_lt_one
#print axioms blankReachesGrowingLoop
end models
end PA194SeedWidthGrowth
