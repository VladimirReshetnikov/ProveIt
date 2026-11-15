import PA194SourceSite27Physical
import PA194SourceSite28Physical
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194Site27PositiveThen28
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
open PA194Site28Complete PA194Site28OutputFile PA194SourceSite28Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem positiveThenIncrement (k tail m : M) (args : Fin 11 → M)
    (hm : args 0 = m+1)
    (htail : args 10 = modelNumeral M PA194StartupSourceFrame.seedTail) :
    let nextArgs := Function.update args 0 m
    let finalArgs := updated nextArgs
    F step ![F step ![sourceState 27 args tail]] = sourceState 29 finalArgs tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) args] =
      physicalFrame 29 (k+1) finalArgs := by
  let nextArgs := Function.update args 0 m
  have ht : nextArgs 10 = modelNumeral M PA194StartupSourceFrame.seedTail := by
    simpa [nextArgs] using htail
  obtain ⟨hsource1,c1,hphysical1⟩ := PA194SourceSite27Physical.positiveBranch k tail m args hm
  obtain ⟨hsource2,c2,hphysical2⟩ := PA194SourceSite28Physical.sourcePhysical k tail nextArgs ht
  constructor
  · rw [hsource1,hsource2]
  · refine ⟨F addCode ![c1,c2],?_⟩
    rw [PA194StepperCompose.modelStepperCompose,hphysical1,hphysical2]
#print axioms positiveThenIncrement
end models
end PA194Site27PositiveThen28
