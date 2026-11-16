import PA194HalfFileSixExact
import PA194FirstFourPositiveExact
import PA194SixteenScanExit
import PA194MarkerReturnCell
import PA194SeventeenToRootControl
import PA194FirstThreeBlankTailTo16
import PA194ZerosDouble
import PA194FourteenComposition
import PA194ZerosEven
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SixteenReturnRun
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SixteenScanExit PA194MarkerReturnCell PA194SeventeenToRootControl PA194FirstFourPositiveExact PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194RegisterFile PA194MarkerScan PA194BinaryDouble
open PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelSixteenReturnRun (n l r : M) :
    let s := F ones ![n,l+l]
    let w := F ones ![n,(1 : M)+r+r]
    F PA194Stepper.stepper ![n+1,F pairCode ![modelNumeral M 16,
      F pairCode ![F halfCode (fun _ => s),F parityCode (fun _ => s)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let s := F ones ![n,l+l]
  let start := F pairCode ![modelNumeral M 17,F pairCode ![s,r+r+1]]
  have hstart : F PA194Stepper.stepper ![(1 : M),start] =
      F pairCode ![modelNumeral M 16,
        F pairCode ![F halfCode (fun _ => s),F parityCode (fun _ => s)+(1+1)+(r+r)+(r+r)]] := by
    rw [←PA194StateOne.modelNumeralOne]
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
    rw [PA194StateOne.modelNumeralOne]
    simpa only [start,show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl] using
      modelPackedMarkerStart (⟨1,by decide⟩ : Fin 2) s r
  have h := modelMarkerReturnCell (⟨1,by decide⟩ : Fin 2) n l r
  dsimp only at h
  have hc : (n+1)+1 = (1 : M)+(n+1) := by simp only [add_comm]
  rw [hc] at h
  change F PA194Stepper.stepper ![F addCode ![(1 : M),n+1],_] = _ at h
  rw [PA194StepperCompose.modelStepperCompose,show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl] at h
  change F PA194Stepper.stepper ![n+1,F PA194Stepper.stepper ![(1 : M),start]] = _ at h
  rw [hstart] at h
  exact h
#print axioms modelSixteenReturnRun
end models
end PA194SixteenReturnRun
