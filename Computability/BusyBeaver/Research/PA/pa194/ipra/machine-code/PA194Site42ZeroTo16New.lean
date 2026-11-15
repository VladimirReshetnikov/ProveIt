import PA194Site42ZeroTo14
import PA194ThirteenExitComposition
import PA194ZeroReturnTo16
import PA194Site32ZeroTo14
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site42ZeroTo16New
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

theorem stretched (u a : M) :
    let l := a+a+1
    let y := F zeros ![(u+1)+1,l+l]
    F zeros ![u,F zeros ![modelNumeral M 3,l]+F zeros ![modelNumeral M 3,l]] = y+y := by
  dsimp only
  have hn : modelNumeral M 3 = modelNumeral M 2+1 := by rw [←modelNumeralOne,←modelNumeralAdd]
  rw [hn,PA194Site32ZeroPath.zerosSucc,PA194HeaderController.zerosTwo]
  rw [PA194Site32ZeroPath.zerosSucc,PA194Site32ZeroPath.zerosSucc]
  repeat rw [PA194ZerosDouble.modelZerosDouble]
theorem zeroTo16 (k : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    let f := F sourceFileCode args
    let n := (k+1)+1
    let z := F zeros ![n,(1 : M)+(f+f)]
    let r := (z+z)+(z+z)
    let c12 := F addCode ![F addCode ![PA194Site42ZeroRollback.cost args,k+1],modelNumeral M 5]
    let c14 := ((modelNumeral M 3+1)+(k+1))+1
    let c16 := ((1 : M)+n)+modelNumeral M 3
    F PA194Stepper.stepper ![F addCode ![F addCode ![c12,c14],c16],PA194Site42Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 12,((1 : M)+1+1)+(r+r)+(r+r)]] := by
  dsimp only
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  let n := (k+1)+1
  let y := F zeros ![n,modelNumeral M 51+modelNumeral M 51]
  have hf : f=p+p := by rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  have h14 := PA194Site42ZeroTo14.zeroTo14 k args hz
  dsimp only at h14
  have h51 : modelNumeral M 51 = modelNumeral M 25+modelNumeral M 25+1 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hl := stretched (k+1) (modelNumeral M 25)
  dsimp only at hl
  rw [←h51] at hl
  conv_rhs at hl => rw [PA194Site32ZeroPath.zerosSucc]
  change F zeros ![k+1,F zeros ![modelNumeral M 3,modelNumeral M 51]+F zeros ![modelNumeral M 3,modelNumeral M 51]] = (y+y)+(y+y) at hl
  rw [hl,(modelDouble (y+y)).1,(modelDouble (y+y)).2,zero_add] at h14
  change _ = F pairCode ![modelNumeral M 14,F pairCode ![y+y,f+f]] at h14
  have h16 := PA194FirstThreeBlankTailTo16.header14To16 n (modelNumeral M 25) p
  dsimp only at h16
  rw [←h51] at h16
  have h25 : modelNumeral M 25 = modelNumeral M 12+modelNumeral M 12+1 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h25,(modelOdd (modelNumeral M 12)).1,(modelOdd (modelNumeral M 12)).2,←hf] at h16
  have hsum : (1 : M)+f+f = (1 : M)+(f+f) := by simp only [add_assoc]
  rw [hsum] at h16
  rw [PA194StepperCompose.modelStepperCompose,h14,h16]
  dsimp only [n,f]
  simp only [add_assoc]
#print axioms zeroTo16
#print axioms stretched
end models
end PA194Site42ZeroTo16New
