import PA194SourceSite45PositivePhysical
import PA194Site45PositivePath
import PA194SourceSite45Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site45PositiveClockExact
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
        (modelNumeral M 8 + (cost + (PA194Site45PositiveTo16.clock k args + modelNumeral M 22)))))))))

theorem exactClock (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    F PA194Stepper.stepper ![clock k args,physicalFrame 45 ((k+1)+1) args] =
      physicalFrame 46 ((k+1)+1) (Function.update args 6 m) := by
  have h := (PA194SourceSite45PositivePhysical.positiveBranch k (0 : M) m args hm).2
  dsimp only [PA194Site45Branch.runTo4] at h
  repeat' rw [←PA194StepperCompose.modelStepperCompose] at h
  change F PA194Stepper.stepper ![clock k args,physicalFrame 45 ((k+1)+1) args] = _ at h
  exact h
#print axioms exactClock
end models
end PA194Site45PositiveClockExact
