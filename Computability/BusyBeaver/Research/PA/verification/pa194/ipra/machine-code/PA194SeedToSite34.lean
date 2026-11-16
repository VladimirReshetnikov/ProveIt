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
namespace PA194SeedToSite34
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

theorem blankTo34 (tail : M) :
    ∃ c0 c1 c2 c3 c d : M,
      F PA194Stepper.stepper ![d,F PA194Stepper.stepper ![c,
        PA194Site36ZeroRun.run (modelNumeral M 40) (PA194SeedToFirstSite36.args36 (M := M))
          (PA194Site35Run.run (modelNumeral M 42) (count35 (M := M)) (next35 (M := M))
            (F PA194Stepper.stepper ![c3,F PA194Stepper.stepper ![c2,F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,modelNumeral M 0]]]]))]] =
        physicalFrame 34 (modelNumeral M 47) (PA194SeedToDrainReturn.afterDrain (M := M)) ∧
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
        PA194SourceSite31Controller.sourceState 38 (PA194SeedToFirstSite36.args36 (M := M)) tail]]]]] =
        PA194SourceSite31Controller.sourceState 34 (PA194SeedToDrainReturn.afterDrain (M := M)) tail := by
  obtain ⟨c0,c1,c2,c3,c,hseed,hcontroller⟩ := PA194SeedToDrainReturn.blankToDrainReturn (M := M) tail
  have hz : PA194SeedToDrainReturn.afterDrain (M := M) 7 = (0 : M) := by
    have h := PA194SourceSite38DrainStep.updatedRegisters (PA194SeedToFirstSite36.args36 (M := M)) (0 : M)
      (F Code.succ (fun _ => count35 (M := M)))
    exact h.1
  obtain ⟨d,hc,hp⟩ := PA194SourceSite38ZeroSingle.zeroSingle (modelNumeral M 41) tail (PA194SeedToDrainReturn.afterDrain (M := M)) hz
  have h43 : (modelNumeral M 41+1)+1 = modelNumeral M 43 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have h47 : (((((modelNumeral M 41+1)+1)+1)+1)+1)+1 = modelNumeral M 47 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  rw [h47,h43] at hp
  refine ⟨c0,c1,c2,c3,c,d,?_,?_⟩
  · rw [hseed]
    exact hp
  · rw [hcontroller]
    exact hc
#print axioms blankTo34
end models
end PA194SeedToSite34
