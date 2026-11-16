import PA194Site34ZeroTo12
import PA194ThirteenExitComposition
import PA194ZeroReturnTo16
import PA194Site32ZeroTo14
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34ZeroTo16
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
  let c12 := F addCode ![F addCode ![PA194Site34ZeroRollback.clock k args,k+1],modelNumeral M 4]
  let c14 := ((modelNumeral M 2+1)+(k+1))+1
  let c16 := ((1 : M)+(k+1))+modelNumeral M 3
  F addCode ![F addCode ![c12,c14],c16]

theorem zeroTo16 (k : M) (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    let f := F sourceFileCode args
    let z := F zeros ![k+1,(1 : M)+(f+f)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 25,(1+1)+(r+r)+(r+r)]] := by
  dsimp only
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  have hf : f=p+p := by rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  let r := F zeros ![k+1,(1 : M)+(f+f)]
  have h12 := PA194Site34ZeroTo12.zeroTo12 k args hz
  dsimp only at h12
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 2) (k+1) (modelNumeral M 101) p
  rw [←hf,PA194HeaderController.zerosTwo] at hs
  have h14 : F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site34ZeroRollback.clock k args,k+1],modelNumeral M 4],
      ((modelNumeral M 2+1)+(k+1))+1],PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 14,F pairCode ![
        F halfCode (fun _ => F zeros ![k+1,F zeros ![modelNumeral M 2,modelNumeral M 101]+F zeros ![modelNumeral M 2,modelNumeral M 101]]),
        F parityCode (fun _ => F zeros ![k+1,F zeros ![modelNumeral M 2,modelNumeral M 101]+F zeros ![modelNumeral M 2,modelNumeral M 101]])+f+f]] := by
    rw [PA194StepperCompose.modelStepperCompose,h12,hs]
  have h16 := PA194ZeroReturnTo16.from14To16 k (modelNumeral M 50) p
  dsimp only at h16
  have h101 : modelNumeral M 50+modelNumeral M 50+1 = modelNumeral M 101 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have h50 : modelNumeral M 50 = modelNumeral M 25+modelNumeral M 25 := by rw [←modelNumeralAdd]
  rw [h101,←hf,h50,(modelDouble (modelNumeral M 25)).1,(modelDouble (modelNumeral M 25)).2,zero_add] at h16
  have hsum : (1 : M)+f+f = (1 : M)+(f+f) := by simp only [add_assoc]
  rw [hsum] at h16
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h14,h16]
#print axioms zeroTo16
end models
end PA194Site34ZeroTo16
