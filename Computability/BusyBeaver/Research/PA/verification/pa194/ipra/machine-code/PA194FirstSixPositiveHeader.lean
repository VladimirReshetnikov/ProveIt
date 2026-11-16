import PA194ZeroFirstReturn
import PA194MarkerReturnCell
import PA194MarkDelimiter
import PA194FourteenComposition
import PA194HeaderController
import PA194SevenReturnController
import PA194FifteenExitComposition
import PA194ZeroRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FirstSixPositiveHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194ZeroFirstReturn PA194MarkerReturnCell PA194BinaryDouble PA194MarkDelimiter PA194FourteenComposition PA194HeaderController PA194StateOne
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194ZeroRuns PA194SevenReturnController
open PA194FifteenExitComposition PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The zero-first-block return reaches the same kind of state-17 header. -/
theorem firstSixTo17 (h r : M) :
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let b := F block ![(0 : M),r+r]
    let t := (1 : M)+(r+r)+(r+r)
    let q := (t+t)+(t+t)
    let w := F ones ![modelNumeral M 4,1+q+q]
    let c := (modelNumeral M 2+(((modelNumeral M 2+1)+(0 : M))+1+1))+modelNumeral M 2
    F PA194Stepper.stepper ![c+((modelNumeral M 4+1)+1),
      F pairCode ![modelNumeral M 7,F pairCode ![a2+a2,b+b]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![h,1+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let t := (1 : M)+(r+r)+(r+r)
  let q := (t+t)+(t+t)
  have hs : F ones ![modelNumeral M 4,xx+xx] = a2 := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have h1 := zeroToOddFifteen (M := M) a2 r
  have h2 := modelMarkerReturnCell ⟨0,by decide⟩ (modelNumeral M 4) xx q
  dsimp only at h1 h2
  rw [hs,(modelOdd h).1,(modelOdd h).2] at h2
  change F PA194Stepper.stepper ![F addCode ![_,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h1]
  exact h2
#print axioms firstSixTo17
end models
end PA194FirstSixPositiveHeader
