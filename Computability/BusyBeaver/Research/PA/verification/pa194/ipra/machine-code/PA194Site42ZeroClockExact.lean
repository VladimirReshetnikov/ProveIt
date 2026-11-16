import PA194SourceSite42ZeroPhysical
import PA194Site42ZeroPath
import PA194SourceSite42Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194Site42ZeroClockExact
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
  let t0 := ((((PA194Site42ZeroRollback.cost args+(k+1))+modelNumeral M 5)+(((modelNumeral M 3+1)+(k+1))+1))+(((1 : M)+((k+1)+1))+modelNumeral M 3))+modelNumeral M 21
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

theorem exactClock (k : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    F PA194Stepper.stepper ![clock k args,physicalFrame 42 ((k+1)+1) args] =
      physicalFrame 45 (((k+1)+1)+1) args := by
  have h := (PA194SourceSite42ZeroPhysical.zeroBranch k (0 : M) args hz).2
  dsimp only [PA194Site42Branch.runTo4] at h
  repeat' rw [←PA194StepperCompose.modelStepperCompose] at h
  change F PA194Stepper.stepper ![clock k args,physicalFrame 42 ((k+1)+1) args] = _ at h
  exact h
#print axioms exactClock
end models
end PA194Site42ZeroClockExact
