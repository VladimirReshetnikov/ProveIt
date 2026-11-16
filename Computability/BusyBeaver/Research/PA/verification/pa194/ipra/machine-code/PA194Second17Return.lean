import PA194ControllerReturn
import PA194UnaryRuns
import PA194BinaryDouble
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Second17Return
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194BinaryDouble PA194ControllerReturn PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- The second state-17 layout returns after scanning four left ones to the k=1 header shape. -/
theorem secondToHeader (g w : M) :
    let h := g+g+1
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let v := F ones ![modelNumeral M 4,(1 : M)+(w+w)+(w+w)]
    F PA194Stepper.stepper ![(modelNumeral M 4+1)+1,
      F pairCode ![modelNumeral M 17,F pairCode ![a2,(1 : M)+(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![h,(1 : M)+(v+v)+(v+v)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let h := g+g+1
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let v := F ones ![modelNumeral M 4,(1 : M)+(w+w)+(w+w)]
  have hl : F ones ![modelNumeral M 4,xx+xx] = a2 := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc,
      show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have hr : (1 : M)+(w+w)+(w+w) = (w+w)+(w+w)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  have hm := PA194MarkerReturnCell.modelMarkerReturnCell ⟨1,by decide⟩ (modelNumeral M 4) xx (w+w)
  dsimp only at hm
  rw [hl,(modelOdd h).1,(modelOdd h).2] at hm
  rw [←hr] at hm
  exact hm
#print axioms secondToHeader
end models
end PA194Second17Return
