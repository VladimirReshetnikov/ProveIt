import PA194IncrementDispatch
import PA194MarkDelimiter
/-! A conditional physical path from dense 113 to the marked-increment entry. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194FirstMarkIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194IncrementDispatch
open PA194MarkDelimiter PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem firstMarkToIncrement (u r : M) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let x := (l+l)+(l+l)
    let markerLeft := x+x+1
    let t0 := r+r+1
    let t1 := t0+t0
    let t2 := t1+t1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let t5 := t4+t4+1
    let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
    let h := g+g+1
    let a0 := h+h+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2+1
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5
    let a7 := a6+a6
    let a8 := a7+a7
    let headerClock := (((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 3+(headerClock+modelNumeral M 9),
      F pairCode ![modelNumeral M 113,F pairCode ![markerLeft+markerLeft+1,(t5+t5+1)+(t5+t5+1)]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![a8,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let z := u+u
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l := z4+z4
  let x := (l+l)+(l+l)
  let markerLeft := x+x+1
  let t0 := r+r+1
  let t1 := t0+t0
  let t2 := t1+t1
  let t3 := t2+t2+1
  let t4 := t3+t3+1
  let t5 := t4+t4+1
  have hm := modelMarkDelimiter (markerLeft+markerLeft+1) t5
  rw [(modelOdd markerLeft).1,(modelOdd markerLeft).2] at hm
  have heq : (1 : M)+((t5+t5)+(t5+t5))+((t5+t5)+(t5+t5)) =
      (((t5+t5)+(t5+t5))+((t5+t5)+(t5+t5)))+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [heq] at hm
  have hd := markerToIncrement ⟨0,by decide⟩ u r
  dsimp only at hd
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,((((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1))+modelNumeral M 9],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hd
#print axioms firstMarkToIncrement
end models
end PA194FirstMarkIncrement
