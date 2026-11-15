import PA194ControllerHaltCharacterization
import PA194SourceSentinel
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ControllerHaltRun
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters PA194SourceRegisterRelation
open PA194SourceInstructionCalibration PA194SourceBoundedStep PA194SourceTargetBounds PA194SourcePCBound
open PA194SourceNoMalformed PA194SourceHaltUnique PA194ControllerHaltCharacterization PA194SourceSentinel PA194IteratedSimulation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem nextHaltValid (s : M)
    (hvalid : F pc ![s] < modelNumeral M 3673 ∨ F pc ![s] = modelNumeral M 3674) :
    F pc ![F step ![s]] = modelNumeral M 3674 ↔
      F pc ![s] = modelNumeral M 10 ∨ F pc ![s] = modelNumeral M 3674 := by
  rcases hvalid with hw | hh
  · rw [nextHaltIffSite10 s hw]
    have hn : F pc ![s] ≠ modelNumeral M 3674 := by
      have hlt := lt_trans hw (modelNumeralStrict 3673 3674 (by decide))
      exact ne_of_lt hlt
    simp only [hn,or_false]
  · rw [stepHalted s hh]
    simp only [hh,or_true]

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem runSuccessorHalt (seed n : M)
    (hvalid : F pc ![F run ![n,seed]] < modelNumeral M 3673 ∨
      F pc ![F run ![n,seed]] = modelNumeral M 3674) :
    F pc ![F run ![n+1,seed]] = modelNumeral M 3674 ↔
      F pc ![F run ![n,seed]] = modelNumeral M 10 ∨
      F pc ![F run ![n,seed]] = modelNumeral M 3674 := by
  rw [run,iterateSucc]
  exact nextHaltValid _ hvalid
#print axioms nextHaltValid
#print axioms runSuccessorHalt
end models
end PA194ControllerHaltRun
