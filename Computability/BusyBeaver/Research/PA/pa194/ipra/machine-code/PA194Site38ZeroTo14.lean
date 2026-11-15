import PA194Site38ZeroTo12
import PA194ThirteenExitComposition
import PA194ZeroReturnTo16
import PA194Site32ZeroTo14
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site38ZeroTo14
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

theorem zeroTo14 (k : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    let f := F sourceFileCode args
    let left := F zeros ![k+1,F zeros ![modelNumeral M 3,modelNumeral M 807]+F zeros ![modelNumeral M 3,modelNumeral M 807]]
    let c12 := F addCode ![F addCode ![PA194Site38ZeroRollback.cost args,k+1],modelNumeral M 5]
    let c14 := ((modelNumeral M 3+1)+(k+1))+1
    F PA194Stepper.stepper ![F addCode ![c12,c14],PA194Site38Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => left),F parityCode (fun _ => left)+f+f]] := by
  dsimp only
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  have hf : f=p+p := by rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  let r := F zeros ![k+1,(1 : M)+(f+f)]
  have h12 := PA194Site38ZeroTo12.zeroTo12 k args hz
  dsimp only at h12
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 3) (k+1) (modelNumeral M 807) p
  have hz3 (x : M) : F zeros ![modelNumeral M 3,x] = ((x+x)+(x+x))+((x+x)+(x+x)) := by
    have hn : modelNumeral M 3 = modelNumeral M 2+1 := by rw [←modelNumeralOne,←modelNumeralAdd]
    rw [hn,PA194Site32ZeroPath.zerosSucc,PA194HeaderController.zerosTwo]
  rw [←hf,hz3] at hs
  have h14 : F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site38ZeroRollback.cost args,k+1],modelNumeral M 5],
      ((modelNumeral M 3+1)+(k+1))+1],PA194Site38Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 14,F pairCode ![
        F halfCode (fun _ => F zeros ![k+1,F zeros ![modelNumeral M 3,modelNumeral M 807]+F zeros ![modelNumeral M 3,modelNumeral M 807]]),
        F parityCode (fun _ => F zeros ![k+1,F zeros ![modelNumeral M 3,modelNumeral M 807]+F zeros ![modelNumeral M 3,modelNumeral M 807]])+f+f]] := by
    rw [PA194StepperCompose.modelStepperCompose,h12,hs]
  exact h14
#print axioms zeroTo14
end models
end PA194Site38ZeroTo14
