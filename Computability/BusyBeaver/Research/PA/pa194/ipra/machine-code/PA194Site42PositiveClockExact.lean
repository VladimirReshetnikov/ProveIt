import PA194SourceSite42PositivePhysical
import PA194Site42PositivePath
import PA194SourceSite42Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site42PositiveClockExact
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
  let vec := PA194Site42MarkedFile.prefixArgs args
  let cost := ((k+1)+F (PA194CarryFile.costCode 5) vec)+modelNumeral M 2
  let t0 := PA194Site42PositiveTo16.clock k args + modelNumeral M 23
  let t1 := cost+t0
  let t2 := modelNumeral M 11+t1
  let t3 := modelNumeral M 24+t2
  let t4 := (((k+1)+1)+1)+t3
  let t5 := ((e 0+1)+1)+t4
  let t6 := ((e 1+1)+1)+t5
  let t7 := ((e 2+1)+1)+t6
  let t8 := ((e 4+1)+((e 3+1)+1))+t7
  let t9 := modelNumeral M 3+t8
  PA194Site42SecondTo14.clock k args+t9

theorem exactClock (k m : M) (args : Fin 11 → M) (hm : args 7 = m+1) :
    F PA194Stepper.stepper ![clock k args,physicalFrame 42 ((k+1)+1) args] =
      physicalFrame 43 ((k+1)+1) (Function.update args 7 m) := by
  have h := (PA194SourceSite42PositivePhysical.positiveBranch k (0 : M) m args hm).2
  dsimp only [PA194Site42Branch.runTo4] at h
  repeat' rw [←PA194StepperCompose.modelStepperCompose] at h
  change F PA194Stepper.stepper ![clock k args,physicalFrame 42 ((k+1)+1) args] = _ at h
  exact h
#print axioms exactClock
end models
end PA194Site42PositiveClockExact
