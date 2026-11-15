import PA194SeedControllerReach29
import PA194SourceSite29Physical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SeedControllerReach30
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters PA194SourceSite25Physical
open PA194StartupSourceFrame PA194RegisterFile PA194SeedControllerReach29
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem blankAndFourSteps (tail : M) :
    let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
    let k : M := modelNumeral M 38
    let args29 := PA194Site28OutputFile.updated (Function.update e 0 (1 : M))
    let args30 := PA194Site29OutputWithCarry.updated args29
    F step ![F step ![F step ![F step ![sourceState 25 e tail]]]] = sourceState 30 args30 tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,modelNumeral M 0] =
      physicalFrame 30 ((k+1)+1) args30 := by
  let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
  let k : M := modelNumeral M 38
  let k39 : M := modelNumeral M 39
  let args29 := PA194Site28OutputFile.updated (Function.update e 0 (1 : M))
  have ht : args29 10 = F block ![(1 : M),modelNumeral M seedTail] := by
    simp [args29,PA194Site28OutputFile.updated]
  have hgap : (k+1)+1 = k39+1 := by
    dsimp only [k,k39]
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  obtain ⟨hs3,c3,hp3⟩ := PA194SeedControllerReach29.blankAndThreeSteps (M := M) tail
  change F step ![F step ![F step ![sourceState 25 e tail]]] = sourceState 29 args29 tail at hs3
  change F PA194Stepper.stepper ![c3,modelNumeral M 0] = physicalFrame 29 (k39+1) args29 at hp3
  obtain ⟨hs4,c4,hp4⟩ := PA194SourceSite29Physical.sourcePhysical k tail args29 ht
  constructor
  · rw [hs3,hs4]
  · refine ⟨F addCode ![c3,c4],?_⟩
    rw [PA194StepperCompose.modelStepperCompose,hp3,←hgap,hp4]
#print axioms blankAndFourSteps
end models
end PA194SeedControllerReach30
