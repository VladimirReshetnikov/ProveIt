import PA194IncrementHeaderReturn
import PA194SevenToSixteen
import PA194HeaderController
import PA194UnaryRuns
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeventeenToRootControl
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194HeaderController PA194IncrementHeaderReturn PA194SevenToSixteen PA194RegisterFile PA194ZeroRuns
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
/-- A state-17 header returns to dense 24 with the same physical halves. -/
theorem returnToControl24 (u w : M) :
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let r := (1 : M)+(w+w)+(w+w)
    F PA194Stepper.stepper ![(((1 : M)+1)+1)+1+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1),
      F pairCode ![modelNumeral M 17,F pairCode ![h,r]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![h,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hm := markerTo24 ⟨1, by decide⟩ (1 : M) u (w+w)
  dsimp only at hm ⊢
  have ho (v : M) : F ones ![(1 : M),v] = v+v+1 := by
    rw [← PA194StateOne.modelNumeralOne]
    change F ones ![F Code.succ (fun _ => modelNumeral M 0),v] = _
    rw [modelOnesSucc,show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero,PA194StateOne.modelNumeralOne]
  rw [ho,ho] at hm
  simp only [zerosTwo,zerosSix] at hm ⊢
  simp only [add_assoc,add_comm,add_left_comm] at hm ⊢
  exact hm
#print axioms returnToControl24
end models
end PA194SeventeenToRootControl
