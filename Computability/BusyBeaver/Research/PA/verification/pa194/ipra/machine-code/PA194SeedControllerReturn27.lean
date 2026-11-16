import PA194SeedControllerReach30
import PA194SourceSite30Physical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SeedControllerReturn27
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters PA194SourceSite25Physical
open PA194StartupSourceFrame PA194RegisterFile PA194SeedControllerReach30
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem blankAndFiveSteps (tail : M) :
    let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
    let k : M := modelNumeral M 38
    let args29 := PA194Site28OutputFile.updated (Function.update e 0 (1 : M))
    let args30 := PA194Site29OutputWithCarry.updated args29
    F step ![F step ![F step ![F step ![F step ![sourceState 25 e tail]]]]] = sourceState 27 args30 tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,modelNumeral M 0] =
      physicalFrame 27 ((((k+1)+1)+1)+1) args30 := by
  let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
  let k : M := modelNumeral M 38
  let args29 := PA194Site28OutputFile.updated (Function.update e 0 (1 : M))
  let args30 := PA194Site29OutputWithCarry.updated args29
  obtain ⟨hs4,c4,hp4⟩ := PA194SeedControllerReach30.blankAndFourSteps (M := M) tail
  change F step ![F step ![F step ![F step ![sourceState 25 e tail]]]] = sourceState 30 args30 tail at hs4
  change F PA194Stepper.stepper ![c4,modelNumeral M 0] = physicalFrame 30 ((k+1)+1) args30 at hp4
  obtain ⟨hs5,hp5⟩ := PA194SourceSite30Physical.sourcePhysical k tail args30
  constructor
  · rw [hs4,hs5]
  · refine ⟨F addCode ![c4,modelNumeral M 40],?_⟩
    rw [PA194StepperCompose.modelStepperCompose,hp4,hp5]
#print axioms blankAndFiveSteps
end models
end PA194SeedControllerReturn27
