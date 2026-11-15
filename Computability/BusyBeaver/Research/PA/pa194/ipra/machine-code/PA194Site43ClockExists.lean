import PA194SourceSite43Physical
import PA194Site43Complete
import PA194SourceSite43Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site43ClockExists
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

theorem existsClock (k count : M) (args : Fin 11 → M)
    (he : PA194RegisterPermutation.physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    ∃ c : M, F PA194Stepper.stepper ![c,physicalFrame 43 ((k+1)+1) args] =
      physicalFrame 44 ((k+1)+1) (PA194Site43OutputFile.updated args count) := by
  have h := (PA194SourceSite43Physical.sourcePhysical k count (0 : M) args he).2
  dsimp only [PA194Site43To7Increment.runTo2] at h
  repeat' rw [←PA194StepperCompose.modelStepperCompose] at h
  exact ⟨_,h⟩
#print axioms existsClock
end models
end PA194Site43ClockExists
