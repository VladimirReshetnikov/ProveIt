import PA194Site3671To69
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194Site32ZeroPath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3671GapDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem oddRow (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 69,F pairCode ![modelNumeral M 14,x+x+1]]] =
      F pairCode ![modelNumeral M 33,F pairCode ![modelNumeral M 7,(x+x+1)+(x+x+1)]] := by
  have h := PA194LeftOneWriteOne.leftOneWriteOne 69 33 (by decide) (by decide +kernel) (modelNumeral M 14) x
  have hn : modelNumeral M 14 = modelNumeral M 7+modelNumeral M 7 := by rw [←modelNumeralAdd]
  rw [hn,(modelDouble (modelNumeral M 7)).1,(modelDouble (modelNumeral M 7)).2] at h
  simp only [zero_add] at h
  rw [←hn] at h
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h]
  simp only [add_assoc,add_comm,add_left_comm]

theorem evenRow (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 69,F pairCode ![modelNumeral M 14,x+x]]] =
      F pairCode ![modelNumeral M 94,F pairCode ![modelNumeral M 7,(x+x)+(x+x)]] := by
  have h := PA194LeftRows.leftZero 69 94 (by decide) (by decide +kernel) (modelNumeral M 14) x
  have hn : modelNumeral M 14 = modelNumeral M 7+modelNumeral M 7 := by rw [←modelNumeralAdd]
  rw [hn,(modelDouble (modelNumeral M 7)).1,(modelDouble (modelNumeral M 7)).2] at h
  simp only [zero_add] at h
  rw [←hn] at h
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h]

theorem zeroGap (args : Fin 11 → M) :
    let f := F sourceFileCode args
    F PA194Stepper.stepper ![modelNumeral M 6,PA194SourceSite31Physical.physicalFrame 3671 (0 : M) args] =
      F pairCode ![modelNumeral M 33,F pairCode ![modelNumeral M 7,(f+f+1)+(f+f+1)]] := by
  dsimp only
  have h := PA194Site3671To69.to69 (0 : M) args
  dsimp only at h
  rw [modelZerosZero] at h
  have hr : (1 : M)+(F sourceFileCode args+F sourceFileCode args) = F sourceFileCode args+F sourceFileCode args+1 := by ac_rfl
  rw [hr] at h
  nth_rewrite 1 [show modelNumeral M 6 = F addCode ![modelNumeral M 5,modelNumeral M 1] from by change modelNumeral M 6 = modelNumeral M 5+modelNumeral M 1; rw [←modelNumeralAdd]]
  rw [PA194StepperCompose.modelStepperCompose,h,oddRow]

theorem positiveGap (gap : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    let rest := F zeros ![gap,(1 : M)+(f+f)]
    F PA194Stepper.stepper ![modelNumeral M 6,PA194SourceSite31Physical.physicalFrame 3671 (gap+1) args] =
      F pairCode ![modelNumeral M 94,F pairCode ![modelNumeral M 7,(rest+rest)+(rest+rest)]] := by
  dsimp only
  have h := PA194Site3671To69.to69 (gap+1) args
  dsimp only at h
  rw [PA194Site32ZeroPath.zerosSucc] at h
  nth_rewrite 1 [show modelNumeral M 6 = F addCode ![modelNumeral M 5,modelNumeral M 1] from by change modelNumeral M 6 = modelNumeral M 5+modelNumeral M 1; rw [←modelNumeralAdd]]
  rw [PA194StepperCompose.modelStepperCompose,h,evenRow]
#print axioms zeroGap
#print axioms positiveGap
end models
end PA194Site3671GapDispatch
