import PA194SixteenScanExit
import PA194UnaryRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194IncrementHeaderReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
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
/-- The state-16 return with four left ones following the increment box. -/
theorem incrementToHeader (h z : M) :
    let xx := h+h+1
    let ll := (xx+xx)+(xx+xx)+1
    let a0 := ll+ll+1
    let a1 := a0+a0+1
    let a2 := a1+a1+1
    let a3 := a2+a2+1
    let r := 1+(z+z)+(z+z)
    let w := F ones ![modelNumeral M 4+1,r]
    F PA194Stepper.stepper ![((modelNumeral M 4)+1)+1,
      F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a3),
        F parityCode (fun _ => a3)+(1+1)+(z+z+(z+z))+(z+z+(z+z))]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![h,1+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let xx := h+h+1
  let ll := (xx+xx)+(xx+xx)+1
  let a0 := ll+ll+1
  let a1 := a0+a0+1
  let a2 := a1+a1+1
  let a3 := a2+a2+1
  let r := 1+(z+z)+(z+z)
  have hs : F ones ![modelNumeral M 4,xx+xx] = a2 := by
    rw [show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelOnesSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelOnesSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelOnesSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelOnesSucc]
    rw [show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero]
  have hright : (1 : M)+(1+1)+(z+z+(z+z))+(z+z+(z+z)) = r+r+1 := by
    dsimp [r]
    simp only [add_assoc,add_comm,add_left_comm]
  have hx := modelScanExit (modelNumeral M 4) xx r
  rw [(modelOdd h).1,(modelOdd h).2] at hx
  rw [(modelOdd a2).1,(modelOdd a2).2,hright,←hs]
  exact hx
#print axioms incrementToHeader
end models
end PA194IncrementHeaderReturn
