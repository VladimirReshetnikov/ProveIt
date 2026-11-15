import PA194SourceSite45ZeroPhysical
import PA194Site45ZeroPath
import PA194SourceSite45Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site45ZeroClockExact
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

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  let e := PA194RegisterPermutation.physicalArgs args
  let vec := PA194Site45MarkedFile.prefixArgs args
  let cost := ((k+1)+F (PA194CarryFile.costCode 8) vec)+modelNumeral M 2
  PA194Site45SecondTo14.clock k args + (modelNumeral M 3 +
    (PA194Site45SecondTo17.sixCost args + (((e 1+1)+1) +
      (((e 0+1)+1) + ((((k+1)+1)+1) + (modelNumeral M 23 +
        (modelNumeral M 8 + (cost + (PA194Site45ZeroTo16.clock k args + modelNumeral M 19)))))))))

theorem exactClock (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    F PA194Stepper.stepper ![clock k args,physicalFrame 45 ((k+1)+1) args] =
      physicalFrame 48 (((k+1)+1)+1) args := by
  have h := (PA194SourceSite45ZeroPhysical.zeroBranch k (0 : M) args hz).2
  dsimp only [PA194Site45Branch.runTo4] at h
  repeat' rw [←PA194StepperCompose.modelStepperCompose] at h
  change F PA194Stepper.stepper ![clock k args,physicalFrame 45 ((k+1)+1) args] = _ at h
  exact h
#print axioms exactClock
end models
end PA194Site45ZeroClockExact
