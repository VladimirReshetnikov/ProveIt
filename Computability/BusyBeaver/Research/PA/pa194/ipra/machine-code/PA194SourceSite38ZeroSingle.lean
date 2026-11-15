import PA194Site38ZeroClockExists
import PA194SourceSite41Physical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite38ZeroSingle
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SourceControllerCode PA194SourceSite31Controller PA194SourceSite31Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem zeroSingle (k tail : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    ∃ c : M,
      F step ![F step ![sourceState 38 args tail]] = sourceState 34 args tail ∧
      F PA194Stepper.stepper ![c,physicalFrame 38 ((k+1)+1) args] =
        physicalFrame 34 ((((((k+1)+1)+1)+1)+1)+1) args := by
  obtain ⟨c38,h38⟩ := PA194Site38ZeroClockExists.existsClock k args hz
  have hc38 := PA194SourceSite38Controller.zeroBranch args tail hz
  have hc41 := (PA194SourceSite41Physical.sourcePhysical ((((k+1)+1)+1)+1) tail args).1
  have hp41 := (PA194SourceSite41Physical.sourcePhysical ((((k+1)+1)+1)+1) tail args).2
  refine ⟨F addCode ![c38,modelNumeral M 34],?_,?_⟩
  · rw [hc38,hc41]
  · rw [PA194StepperCompose.modelStepperCompose,h38,hp41]
#print axioms zeroSingle
end models
end PA194SourceSite38ZeroSingle
