import PA194SourceSite38ZeroPhysical
import PA194Site38ZeroPath
import PA194SourceSite38Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site38ZeroClockExists
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

theorem existsClock (k : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    ∃ c : M, F PA194Stepper.stepper ![c,physicalFrame 38 ((k+1)+1) args] =
      physicalFrame 41 ((((k+1)+1)+1)+1) args := by
  have h := (PA194SourceSite38ZeroPhysical.zeroBranch k (0 : M) args hz).2
  dsimp only [PA194Site38Branch.runTo4] at h
  repeat' rw [←PA194StepperCompose.modelStepperCompose] at h
  exact ⟨_,h⟩
#print axioms existsClock
end models
end PA194Site38ZeroClockExists
