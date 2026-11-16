import PA194Site3661SecondTo68
import PA194Site3661GapScan
import PA194HalfFileWithTail
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3661SecondTo93
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

theorem to93 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let r := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
    let a := F ones ![k,modelNumeral M 216]
    let b := a+a+1+(a+a+1)+1
    F PA194Stepper.stepper ![F addCode ![F addCode ![PA194Site3661SecondTo68.firstClock k,modelNumeral M 7],((k+1)+1)+1],
      PA194SourceSite31Physical.physicalFrame 3661 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 93,F pairCode ![b+b,r]] := by
  dsimp only
  let e := physicalArgs args
  let r := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  have hf : f = r+r := by
    dsimp only [f,r,e]
    rw [modelSourceFile,modelFileSucc,modelBlock]
  have h := PA194Site3661SecondTo68.to68 k args
  dsimp only at h
  have scan := PA194Site3661GapScan.scan k (modelNumeral M 216) f r hf
  dsimp only at scan
  rw [PA194StepperCompose.modelStepperCompose,h,scan]
#print axioms to93
end models
end PA194Site3661SecondTo93
