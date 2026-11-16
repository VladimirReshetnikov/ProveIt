import PA194SeedToSite34
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
namespace PA194SeedAfterDrainValues
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

theorem reg7Zero : PA194SeedToDrainReturn.afterDrain (M := M) 7 = (0 : M) := by
  have h := PA194SourceSite38DrainStep.updatedRegisters (PA194SeedToFirstSite36.args36 (M := M)) (0 : M)
    (F Code.succ (fun _ => count35 (M := M)))
  exact h.1

theorem reg6One : PA194SeedToDrainReturn.afterDrain (M := M) 6 = (1 : M) := by
  have h := (PA194SourceSite38DrainStep.updatedRegisters (PA194SeedToFirstSite36.args36 (M := M)) (0 : M)
    (F Code.succ (fun _ => count35 (M := M)))).2.1
  rw [PA194SeedToFirstSite36.reg6Zero,zero_add] at h
  exact h

theorem reg8One : PA194SeedToDrainReturn.afterDrain (M := M) 8 = (1 : M) := by
  simp [PA194SeedToDrainReturn.afterDrain,PA194Site39OutputFile.updated,PA194SeedToFirstSite36.args36,
    PA194Site35OutputFile.updated,next35]
#print axioms reg7Zero
#print axioms reg6One
#print axioms reg8One
end models
end PA194SeedAfterDrainValues
