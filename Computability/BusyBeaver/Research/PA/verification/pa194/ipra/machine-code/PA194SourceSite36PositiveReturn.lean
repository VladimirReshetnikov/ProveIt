import PA194Site36PositiveClockExists
import PA194SourceSite37Physical
import PA194SourceSite41Physical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite36PositiveReturn
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

theorem positiveReturn (k tail m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    let out := Function.update args 6 m
    ∃ c : M,
      F step ![F step ![F step ![sourceState 36 args tail]]] = sourceState 34 out tail ∧
      F PA194Stepper.stepper ![c,physicalFrame 36 ((k+1)+1) args] =
        physicalFrame 34 (((((((k+1)+1)+1)+1)+1)+1)+1) out := by
  dsimp only
  let out := Function.update args 6 m
  obtain ⟨c36,h36⟩ := PA194Site36PositiveClockExists.existsClock k m args hm
  have hc36 := PA194SourceSite36Controller.positiveBranch args tail m hm
  have h37 := PA194SourceSite37Physical.sourcePhysical (((k+1)+1)+1) tail out
  have h41 := PA194SourceSite41Physical.sourcePhysical (((((k+1)+1)+1)+1)+1) tail out
  refine ⟨F addCode ![F addCode ![c36,modelNumeral M 38],modelNumeral M 34],?_,?_⟩
  · rw [hc36,h37.1,h41.1]
  · rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h36,h37.2,h41.2]
#print axioms positiveReturn
end models
end PA194SourceSite36PositiveReturn
