import PA194Site27PositiveThen28
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194Site25Then27Then28
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
open PA194Site28OutputFile PA194SourceSite28Physical PA194Site27PositiveThen28
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroPositiveIncrement (k tail m : M) (args : Fin 11 → M)
    (hz : args 8 = (0 : M)) (hm : args 0 = m+1)
    (htail : args 10 = modelNumeral M PA194StartupSourceFrame.seedTail) :
    let finalArgs := updated (Function.update args 0 m)
    F step ![F step ![F step ![sourceState 25 args tail]]] = sourceState 29 finalArgs tail ∧
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 25 (((k+1)+1)+1) args] =
      physicalFrame 29 (k+1) finalArgs := by
  obtain ⟨hsource1,c1,hphysical1⟩ := PA194SourceSite25Physical.zeroBranch (k+1) tail args hz
  obtain ⟨hsource2,c2,hphysical2⟩ := PA194Site27PositiveThen28.positiveThenIncrement k tail m args hm htail
  constructor
  · rw [hsource1,hsource2]
  · refine ⟨F addCode ![c1,c2],?_⟩
    rw [PA194StepperCompose.modelStepperCompose,hphysical1,hphysical2]
#print axioms zeroPositiveIncrement
end models
end PA194Site25Then27Then28
