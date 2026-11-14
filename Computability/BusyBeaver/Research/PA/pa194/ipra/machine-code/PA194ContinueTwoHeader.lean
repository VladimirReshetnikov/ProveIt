import PA194ContinueTwoDispatch
import PA194PositiveThreshold
import PA194SeventeenToRootControl
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ContinueTwoHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194OnesCommute PA194ContinueTwoDispatch PA194FiniteControls PA194PositiveMarkerRoute PA194PositiveThreshold PA194MarkerReturnCell PA194HeaderController PA194StateOne PA194SeventeenToRootControl PA194ZeroRuns
open BinaryTapeCodes PA194UnaryRuns PA194SixteenScanExit PA194BinaryDouble
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
/-- Apply the 32-step result to the concrete header returned by the previous
controller, for an arbitrary model-valued suffix. -/
theorem continueHeader (u z : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let w := F ones ![modelNumeral M 4+1,1+(z+z)+(z+z)]
    let r := z+z
    let t := (r+r)+(r+r)
    let v := F ones ![modelNumeral M 3,(1 : M)+t+t]
    F PA194Stepper.stepper ![modelNumeral M 32,
      F pairCode ![modelNumeral M 24,F pairCode ![h,1+(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,1+(v+v)+(v+v)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let r := z+z
  let t0 := r+r+1
  let t1 := t0+t0+1
  let t2 := t1+t1+1
  let t3 := t2+t2+1
  let t4 := t3+t3+1
  have hw : F ones ![modelNumeral M 4+1,1+(z+z)+(z+z)] = t4+t4+1 := by
    have ha : (1 : M)+(z+z)+(z+z) = r+r+1 := by dsimp [r]; simp only [add_assoc,add_comm,add_left_comm]
    rw [ha,modelOnesCommute]
    have hb : F ones ![modelNumeral M 4+1,r] = t4 := by
      rw [show modelNumeral M 4+1 = F Code.succ (fun _ => modelNumeral M 4) from by
          change F addCode ![modelNumeral M 4,F oneCode Fin.elim0] = _
          rw [modelAddOne],modelOnesSucc,
        show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc,
        show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
        show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
        show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
        show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
    rw [hb]
  have hm := continueTwo32 (M := M) u r
  rw [hw]
  have he (b : M) : (1 : M)+(b+b)+(b+b) = (b+b)+(b+b)+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [he]
  exact hm
#print axioms continueHeader
end models
end PA194ContinueTwoHeader
