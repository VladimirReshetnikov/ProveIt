import PA194SixteenReturnRun
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
namespace PA194SixteenTwoRuns
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194SixteenReturnRun PA194SixteenScanExit PA194MarkerReturnCell PA194SeventeenToRootControl PA194FirstFourPositiveExact PA194FirstFourPositiveTo15 PA194FirstFourPositiveTo14 PA194ZerosEven PA194FirstFourPositiveReturn PA194FirstFourPositiveSelected PA194SevenReturnController PA194ReturnCell PA194ReturnFile PA194OnesCommute
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

theorem modelSixteenTwoRuns (n m l r : M) :
    let z := F ones ![m+1,l+l]
    let s := F ones ![n,z+z]
    let w := F ones ![n,(1 : M)+r+r]
    let v := F ones ![m,(1 : M)+(w+w)+(w+w)]
    F PA194Stepper.stepper ![(n+1)+((m+1)+1),F pairCode ![modelNumeral M 16,
      F pairCode ![F halfCode (fun _ => s),F parityCode (fun _ => s)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(v+v)+(v+v)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := F ones ![m,l+l]
  let z := F ones ![m+1,l+l]
  let w := F ones ![n,(1 : M)+r+r]
  have hz : z=x+x+1 := by
    change F ones ![F addCode ![m,F oneCode Fin.elim0],l+l] = _
    rw [modelAddOne,modelOnesSucc]
  have h1 := modelSixteenReturnRun n z r
  dsimp only at h1
  rw [hz,(modelOdd x).1,(modelOdd x).2] at h1
  rw [←hz] at h1
  have h2 := modelMarkerReturnCell (⟨1,by decide⟩ : Fin 2) m l (w+w)
  dsimp only at h2
  rw [show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl] at h2
  have hw : (1 : M)+(w+w)+(w+w) = (w+w)+(w+w)+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [←hw] at h2
  change F PA194Stepper.stepper ![F addCode ![n+1,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1]
  exact h2
#print axioms modelSixteenTwoRuns
end models
end PA194SixteenTwoRuns
