import PA194MarkerReturnCell
import PA194SixteenTwoRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site35MarkerReturnNext
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194MarkerReturnCell PA194SixteenTwoRuns
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

theorem modelMarkerReturnNext (m l w : M) :
    let z := F ones ![m+1,l+l]
    let v := F ones ![m,(1 : M)+(w+w)+(w+w)]
    F PA194Stepper.stepper ![(m+1)+1,F pairCode ![modelNumeral M 17,
      F pairCode ![F halfCode (fun _ => z),F parityCode (fun _ => z)+(w+w)+(w+w)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(v+v)+(v+v)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let x := F ones ![m,l+l]
  have hz : F ones ![m+1,l+l] = x+x+1 := by
    change F ones ![F addCode ![m,F oneCode Fin.elim0],l+l] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hz,(modelOdd x).1,(modelOdd x).2]
  have h := modelMarkerReturnCell (⟨1,by decide⟩ : Fin 2) m l (w+w)
  dsimp only at h
  rw [show returnControl (⟨1,by decide⟩ : Fin 2) = 17 from rfl] at h
  have hw : (1 : M)+(w+w)+(w+w) = (w+w)+(w+w)+1 := by
    simp only [add_assoc,add_comm,add_left_comm]
  rw [←hw] at h
  exact h
#print axioms modelMarkerReturnNext
end models
end PA194Site35MarkerReturnNext
