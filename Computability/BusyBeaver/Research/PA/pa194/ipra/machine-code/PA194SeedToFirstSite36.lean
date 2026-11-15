import PA194SeedToFirstSite35
import PA194Site35Run
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194SeedToFirstSite36
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ModelLoopIteration PA194ModelLoopState PA194ModelLoopFrame PA194ModelLoopCost PA194ModelSourceLoop PA194ActualSourceLoop PA194ControllerLoopFrame PA194ZeroRuns PA194UnaryRuns PA194BinaryDouble BinaryTapeCodes PackedDecoderModel PA194RegisterFile PA194Path27Header PA194SeedToFirstSite35 PA194ModelSourceLoop PA194ActualLoopOrbit PA194SourceSite31Physical PA194RegisterPermutation PA194OneSpareReturn PA194StateOne PA194FiniteControls PRAExhaustion TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def args36 : Fin 11 → M := PA194Site35OutputFile.updated (next35 (M := M)) (count35 (M := M))

theorem reg6Zero : args36 (M := M) 6 = (0 : M) := by
  have hz : F subCode ![r31 (M := M) 6,r31 6] = (0 : M) := by rw [modelSubAsTsub]; simp
  simpa [args36,PA194Site35OutputFile.updated,next35,out34,PA194Site31OutputFile.updated,frameArgs,
    PA194ActualSourceLoop.args,PA194ModelRestoreSource.running] using hz

theorem blankTo36 (tail : M) :
    ∃ c0 c1 c2 c3 : M,
      PA194Site35Run.run (modelNumeral M 42) (count35 (M := M)) (next35 (M := M))
        (F PA194Stepper.stepper ![c3,F PA194Stepper.stepper ![c2,F PA194Stepper.stepper ![c1,F PA194Stepper.stepper ![c0,modelNumeral M 0]]]]) =
        physicalFrame 36 (modelNumeral M 42) (args36 (M := M)) := by
  obtain ⟨c0,c1,c2,c3,h35,hsuffix⟩ := PA194SeedToFirstSite35.blankTo35 (M := M) tail
  refine ⟨c0,c1,c2,c3,?_⟩
  rw [h35]
  exact PA194Site35Run.correct (modelNumeral M 42) (count35 (M := M)) (next35 (M := M)) hsuffix
#print axioms reg6Zero
#print axioms blankTo36
end models
end PA194SeedToFirstSite36
