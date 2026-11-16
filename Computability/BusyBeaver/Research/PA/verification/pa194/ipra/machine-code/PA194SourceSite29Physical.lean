import PA194SourceSite29Controller
import PA194Site29Complete
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceSite29Physical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
open PA194RegisterPermutation PA194RegisterFile PA194SourceSite29Controller
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem sourcePhysical (k tail : M) (args : Fin 11 → M)
    (htail : args 10 = F block ![(1 : M),modelNumeral M PA194StartupSourceFrame.seedTail]) :
    F step ![sourceState 29 args tail] = sourceState 30 (PA194Site29OutputWithCarry.updated args) tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 29 ((k+1)+1) args] =
      physicalFrame 30 ((k+1)+1) (PA194Site29OutputWithCarry.updated args) := by
  have hs : physicalArgs args 10 = F block ![(1 : M),modelNumeral M PA194StartupSourceFrame.seedTail] := by
    rw [sourceSuffixAt]
    exact htail
  have hp := PA194Site29Complete.complete k args hs
  dsimp only at hp
  simp only [←PA194StepperCompose.modelStepperCompose] at hp
  refine ⟨controllerStep args tail,?_⟩
  exact ⟨_,hp⟩
#print axioms sourcePhysical
end models
end PA194SourceSite29Physical
