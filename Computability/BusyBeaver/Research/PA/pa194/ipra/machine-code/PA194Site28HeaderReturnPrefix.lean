import PA194Site28HeaderTo17
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28HeaderReturnPrefix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194LeftOneWriteOne PA194LeftRows PA194SeedHeaderTo21 PA194BinaryDouble PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem seventeenOneEvenLeft (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 17 16 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem sixteenZeroOddLeft (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![l,(r+r)+(r+r)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 16 17 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem fourReturnSteps (l w : M) :
    let a2 := l+l
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4
    let w1 := w+w
    let x := (w1+w1)+1
    let x1 := x+x
    let y := (x1+x1)+1
    let y1 := y+y
    F PA194Stepper.stepper ![modelNumeral M 4,F pairCode ![modelNumeral M 17,F pairCode ![a5,x]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![l,y1+y1]] := by
  dsimp only
  have heven := rowEvenLeft (M := M) 16 17 (by decide) (by decide +kernel)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 3),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,
      seventeenOneEvenLeft,sixteenZeroOddLeft,seventeenOneEvenLeft,heven]
#print axioms seventeenOneEvenLeft
#print axioms sixteenZeroOddLeft
#print axioms fourReturnSteps
end models
end PA194Site28HeaderReturnPrefix
