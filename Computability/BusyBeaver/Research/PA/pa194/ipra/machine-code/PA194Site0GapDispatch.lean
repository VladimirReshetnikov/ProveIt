import PA194Site0To73
import PA194RightRows
import PA194Site32ZeroPath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site0GapDispatch
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
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 73,F pairCode ![modelNumeral M 64,x+x+1]]] =
      F pairCode ![modelNumeral M 85,F pairCode ![modelNumeral M 128,x]] := by
  have h := rightOne 73 0 85 (by decide) (by decide +kernel) (modelNumeral M 64) x
  have hn : modelNumeral M 64+modelNumeral M 64+modelNumeral M 0 = modelNumeral M 128 := by rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h]

theorem evenRow (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 73,F pairCode ![modelNumeral M 64,x+x]]] =
      F pairCode ![modelNumeral M 59,F pairCode ![modelNumeral M 128,x]] := by
  have h := rightZero 73 0 59 (by decide) (by decide +kernel) (modelNumeral M 64) x
  have hn : modelNumeral M 64+modelNumeral M 64+modelNumeral M 0 = modelNumeral M 128 := by rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h]

theorem zeroGap (args : Fin 11 → M) :
    F PA194Stepper.stepper ![modelNumeral M 7,PA194SourceSite31Physical.physicalFrame 0 (0 : M) args] =
      F pairCode ![modelNumeral M 85,F pairCode ![modelNumeral M 128,F sourceFileCode args]] := by
  have h := PA194Site0To73.to73 (0 : M) args
  dsimp only at h
  rw [modelZerosZero] at h
  have hr : (1 : M)+(F sourceFileCode args+F sourceFileCode args) = F sourceFileCode args+F sourceFileCode args+1 := by ac_rfl
  rw [hr] at h
  nth_rewrite 1 [show modelNumeral M 7 = F addCode ![modelNumeral M 6,modelNumeral M 1] from by change modelNumeral M 7 = modelNumeral M 6+modelNumeral M 1; rw [←modelNumeralAdd]]
  rw [PA194StepperCompose.modelStepperCompose,h,oddRow]

theorem positiveGap (gap : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    let rest := F zeros ![gap,(1 : M)+(f+f)]
    F PA194Stepper.stepper ![modelNumeral M 7,PA194SourceSite31Physical.physicalFrame 0 (gap+1) args] =
      F pairCode ![modelNumeral M 59,F pairCode ![modelNumeral M 128,rest]] := by
  dsimp only
  have h := PA194Site0To73.to73 (gap+1) args
  dsimp only at h
  rw [PA194Site32ZeroPath.zerosSucc] at h
  nth_rewrite 1 [show modelNumeral M 7 = F addCode ![modelNumeral M 6,modelNumeral M 1] from by change modelNumeral M 7 = modelNumeral M 6+modelNumeral M 1; rw [←modelNumeralAdd]]
  rw [PA194StepperCompose.modelStepperCompose,h,evenRow]
#print axioms zeroGap
#print axioms positiveGap
end models
end PA194Site0GapDispatch
