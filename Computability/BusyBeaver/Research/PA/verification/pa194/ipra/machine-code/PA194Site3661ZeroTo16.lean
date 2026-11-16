import PA194Site3661ZeroTo12
import PA194ThirteenExitComposition
import PA194ZeroReturnTo16
import PA194Site32ZeroTo14
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3661ZeroTo16
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  let c12 := F addCode ![F addCode ![PA194Site3661ZeroRollback.cost args,k+1],modelNumeral M 4]
  let c14 := ((modelNumeral M 2+1)+(k+1))+1
  let c16 := ((1 : M)+(k+1))+modelNumeral M 3
  F addCode ![F addCode ![c12,c14],c16]

theorem zeroTo16 (k : M) (args : Fin 11 → M) (hz : args 1 = (0 : M)) :
    let f := F sourceFileCode (args)
    let z := F zeros ![k+1,(1 : M)+(f+f)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![clock k args,PA194Site3661Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 13,(1+1+1)+(r+r)+(r+r)]] := by
  dsimp only
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  have hf : f=p+p := by rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  have h12 := PA194Site3661ZeroTo12.zeroTo12 k args hz
  dsimp only at h12
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 2) (k+1) (modelNumeral M 55) p
  rw [←hf,PA194HeaderController.zerosTwo] at hs
  have hsum : (1 : M)+f+f = (1 : M)+(f+f) := by simp only [zero_add,add_assoc]
  have h16 := PA194ZeroReturnTo16.from14To16 k (modelNumeral M 27) p
  dsimp only at h16
  have h201 : modelNumeral M 27+modelNumeral M 27+1 = modelNumeral M 55 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have h100 : modelNumeral M 27 = modelNumeral M 13+modelNumeral M 13+1 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h201,←hf,h100,(modelOdd (modelNumeral M 13)).1,(modelOdd (modelNumeral M 13)).2] at h16
  rw [hsum] at h16
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h12,hs,h16]
  dsimp only [f]
  simp only [zero_add,add_assoc]
#print axioms zeroTo16
end models
end PA194Site3661ZeroTo16
