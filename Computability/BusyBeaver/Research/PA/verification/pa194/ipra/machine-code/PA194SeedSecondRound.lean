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
namespace PA194SeedSecondRound
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

noncomputable def countAfterDrain : M := F Code.succ (fun _ => F Code.succ (fun _ => count35 (M := M)))
noncomputable def afterRound : Fin 11 → M := Function.update (PA194Site35OutputFile.updated (Function.update (PA194SeedToDrainReturn.afterDrain (M := M)) 8 (0 : M)) (countAfterDrain (M := M))) 6 (0 : M)
theorem suffix : physicalArgs (PA194SeedToDrainReturn.afterDrain (M := M)) 10 = F repeatOutput ![countAfterDrain (M := M),(0 : M)] := by
  simp [physicalArgs,inputOrder,PA194SeedToDrainReturn.afterDrain,PA194Site39OutputFile.updated,countAfterDrain]
theorem blankToNext34 (tail : M) :
    ∃ c0 c1 c2 c3 c d e : M,
      F PA194Stepper.stepper ![e,F PA194Stepper.stepper ![d,F PA194Stepper.stepper ![c,
        PA194Site36ZeroRun.run (modelNumeral M 40) (PA194SeedToFirstSite36.args36 (M := M))
          (PA194Site35Run.run (modelNumeral M 42) (count35 (M := M)) (next35 (M := M))
            (F PA194Stepper.stepper ![c3,F PA194Stepper.stepper ![c2,F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,modelNumeral M 0]]]]))]]] =
        physicalFrame 34 (modelNumeral M 49) (afterRound (M := M)) ∧
      F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![
        PA194SourceSite31Controller.sourceState 34 (PA194SeedToDrainReturn.afterDrain (M := M)) tail]]]]] =
        PA194SourceSite31Controller.sourceState 34 (afterRound (M := M)) tail := by
  obtain ⟨c0,c1,c2,c3,c,d,hseed,_⟩ := PA194SeedToSite34.blankTo34 (M := M) tail
  have h6 : PA194SeedToDrainReturn.afterDrain (M := M) 6 = (0 : M)+1 := by rw [zero_add]; exact PA194SeedAfterDrainValues.reg6One
  have h8 : PA194SeedToDrainReturn.afterDrain (M := M) 8 = (0 : M)+1 := by rw [zero_add]; exact PA194SeedAfterDrainValues.reg8One
  obtain ⟨e,hc,hp⟩ := PA194SourcePositiveDecoderSingle.positiveSingle (modelNumeral M 42)
    (countAfterDrain (M := M)) tail (0 : M) (0 : M) (PA194SeedToDrainReturn.afterDrain (M := M)) h6 h8 suffix
  have h47 : (((((modelNumeral M 42+1)+1)+1)+1)+1) = modelNumeral M 47 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  have h49 : (((((((modelNumeral M 42+1)+1)+1)+1)+1)+1)+1) = modelNumeral M 49 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  rw [h49,h47] at hp
  refine ⟨c0,c1,c2,c3,c,d,e,?_,?_⟩
  · rw [hseed]
    exact hp
  · exact hc
#print axioms suffix
#print axioms blankToNext34
end models
end PA194SeedSecondRound
