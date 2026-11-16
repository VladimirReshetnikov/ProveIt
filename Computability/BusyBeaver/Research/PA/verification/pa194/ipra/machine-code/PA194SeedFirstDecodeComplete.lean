import PA194SeedSecondRound
import PA194SourceSite34ZeroPhysical
import PA194SeedAfterDrainValues
import PA194SourcePositiveDecoderSingle
import PA194SeedToDrainReturn
import PA194SourceSite38ZeroSingle
import PA194SeedSite38Guard
import PA194SourceSite38DrainSingle
import PA194SeedToFirstSite38
import PA194SourceSite38DrainStep
import PA194SeedToFirstSite35
import PA194Site35Run
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedFirstDecodeComplete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ControllerLoopFrame PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble BinaryTapeCodes PackedDecoderModel PA194RegisterFile PA194Path27Header PA194SeedToFirstSite35 PA194ModelSourceLoop PA194ActualLoopOrbit PA194SourceSite31Physical PA194RegisterPermutation PA194OneSpareReturn PA194StateOne PA194FiniteControls PRAExhaustion TableDispatch PRAModelIOpenPairing
open PA194SeedFrameAlignment PA194StartupSourceFrame
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem reg8Zero : PA194SeedSecondRound.afterRound (M := M) 8 = (0 : M) := by
  simp [PA194SeedSecondRound.afterRound,PA194Site35OutputFile.updated]

theorem blankTo42 (tail : M) :
    ∃ c0 c1 c2 c3 c d e : M,
      F PA194Stepper.stepper ![F addCode ![PA194Site34ZeroTo16.clock (modelNumeral M 47) (PA194SeedSecondRound.afterRound (M := M)),modelNumeral M 22],
        F PA194Stepper.stepper ![e,F PA194Stepper.stepper ![d,F PA194Stepper.stepper ![c,
          PA194Site36ZeroRun.run (modelNumeral M 40) (PA194SeedToFirstSite36.args36 (M := M))
            (PA194Site35Run.run (modelNumeral M 42) (count35 (M := M)) (next35 (M := M))
              (F PA194Stepper.stepper ![c3,F PA194Stepper.stepper ![c2,F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,modelNumeral M 0]]]]))]]]] =
        physicalFrame 42 (modelNumeral M 49) (PA194SeedSecondRound.afterRound (M := M)) ∧
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
        PA194SourceSite31Controller.sourceState 34 (PA194SeedToDrainReturn.afterDrain (M := M)) tail]]]]]] =
        PA194SourceSite31Controller.sourceState 42 (PA194SeedSecondRound.afterRound (M := M)) tail := by
  obtain ⟨c0,c1,c2,c3,c,d,e,hseed,hcontroller⟩ := PA194SeedSecondRound.blankToNext34 (M := M) tail
  have hzero := PA194SourceSite34ZeroPhysical.zeroBranch (modelNumeral M 47) tail (PA194SeedSecondRound.afterRound (M := M)) reg8Zero
  have h49 : (modelNumeral M 47+1)+1 = modelNumeral M 49 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h49] at hzero
  refine ⟨c0,c1,c2,c3,c,d,e,?_,?_⟩
  · rw [hseed]
    exact hzero.2
  · rw [hcontroller]
    exact hzero.1
#print axioms reg8Zero
#print axioms blankTo42
end models
end PA194SeedFirstDecodeComplete
