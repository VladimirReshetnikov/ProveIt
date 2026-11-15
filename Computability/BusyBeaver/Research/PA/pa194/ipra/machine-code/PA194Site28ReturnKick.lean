import PA194Site28BlankExit
import PA194LeftOneWriteOne
import PA194LeftRows
import PA194ReturnCell
import PA194StepperCompose
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28ReturnKick
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194LeftOneWriteOne PA194LeftRows PA194ReturnCell PA194BinaryDouble PA194UnaryRuns PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem sevenOneEvenLeft (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 7,F pairCode ![l+l,r+r+1]]) =
    F pairCode ![modelNumeral M 6,F pairCode ![l,(r+r+1)+(r+r+1)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftOneWriteOne 7 6 (by decide) (by decide +kernel) (l+l) r
  rw [(modelDouble l).1,(modelDouble l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem sixZeroOddLeft (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 6,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 7,F pairCode ![l,(r+r)+(r+r)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 6 7 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem twoTo7 (n l t : M) :
    let a := F ones ![n,l+l]
    let b := F ones ![n+1,l+l]
    let s := t+t+1
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 7,F pairCode ![b+b,s]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![a,(s+s)+(s+s)+1]] := by
  dsimp only
  let a := F ones ![n,l+l]
  have hb : F ones ![n+1,l+l] = a+a+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hb]
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,sevenOneEvenLeft,sixZeroOddLeft]

theorem kickReturn (n l t : M) :
    let b := F ones ![n+1,l+l]
    let s := t+t+1
    let q := s+s
    let a := F ones ![n,(1 : M)+q+q]
    F PA194Stepper.stepper ![modelNumeral M 2+((n+1)+1),F pairCode ![modelNumeral M 7,F pairCode ![b+b,s]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(a+a)+(a+a)]] := by
  dsimp only
  let s := t+t+1
  let q := s+s
  have h2 := twoTo7 (M := M) n l t
  dsimp only at h2
  have hr := modelReturnCell n l q
  dsimp only at hr
  have hright : (s+s)+(s+s)+1 = q+q+1 := rfl
  rw [hright] at h2
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,(n+1)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h2,hr]
#print axioms kickReturn
end models
end PA194Site28ReturnKick
