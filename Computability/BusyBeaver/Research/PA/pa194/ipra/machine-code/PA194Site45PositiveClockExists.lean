import PA194SourceSite45PositivePhysical
import PA194Site45PositivePath
import PA194SourceSite45Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site45PositiveClockExists
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

theorem existsClock (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    ∃ c : M, F PA194Stepper.stepper ![c,physicalFrame 45 ((k+1)+1) args] =
      physicalFrame 46 ((k+1)+1) (Function.update args 6 m) := by
  have h := (PA194SourceSite45PositivePhysical.positiveBranch k (0 : M) m args hm).2
  dsimp only [PA194Site45Branch.runTo4] at h
  repeat' rw [←PA194StepperCompose.modelStepperCompose] at h
  exact ⟨_,h⟩
#print axioms existsClock
end models
end PA194Site45PositiveClockExists
