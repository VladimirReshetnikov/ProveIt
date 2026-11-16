import PA194Site29To84
import PA194Site28ThirdDispatch
import PA194Site29HeaderDispatch
import PA194Site28To84
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ThirdDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194UnaryRuns PA194Site29To84 PA194Site28ThirdDispatch TableDispatch PA194Site28To84 PA194Site29HeaderDispatch PA194SeedHeaderTo21 PA194RightRows PA194LeftRows PA194LeftOneWriteOne PA194BinaryDouble PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem elevenTo2 (l t : M) :
    let w := t+t+1
    let s := w+w
    let r := s+s
    let h := r+r+1
    let a := l+l
    let b := a+a+1
    let c := b+b+1
    let d := c+c
    F PA194Stepper.stepper ![modelNumeral M 11,F pairCode ![modelNumeral M 115,
      F pairCode ![l+l,h+h+1]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![(d+d)+(d+d),t]] := by
  dsimp only
  have h69 := rowEvenLeft (M := M) 69 94 (by decide) (by decide +kernel)
  have h70 := PA194Site28ThirdDispatch.row70one (M := M)
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 10),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 10 = F Code.succ (fun _ => modelNumeral M 9) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 9 = F Code.succ (fun _ => modelNumeral M 8) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 8 = F Code.succ (fun _ => modelNumeral M 7) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 7 = F Code.succ (fun _ => modelNumeral M 6) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 6 = F Code.succ (fun _ => modelNumeral M 5) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,
      row115oneEven,
      row67zero,
      row86one,
      row107one,
      row30zeroOdd,
      row36one,
      row49zero,
      h69,
      row94zero,
      row50zero,
      h70]
  rfl
theorem nineteenTo2 (l t : M) :
    let w := t+t+1
    let s := w+w
    let r := s+s
    let u0 := r+r+1
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let b := (a4+a4)+(a4+a4)+1
    let c := b+b+1
    let d := c+c
    F PA194Stepper.stepper ![modelNumeral M 19,F pairCode ![modelNumeral M 24,
      F pairCode ![l,u6+u6+1]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![(d+d)+(d+d),t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let w := t+t+1
  let r := (w+w)+(w+w)
  let h := r+r+1
  have h8 := PA194Site29HeaderDispatch.eightSteps (M := M) l r
  dsimp only at h8
  have h11 := elevenTo2 (M := M) a4 t
  dsimp only at h11
  have heq : (1 : M)+(1+1)+(r+r)+(r+r) = h+h+1 := by
    dsimp only [h]
    simp only [add_assoc,add_comm,add_left_comm]
  rw [heq] at h8
  rw [show modelNumeral M 19 = modelNumeral M 8+modelNumeral M 11 by rw [←modelNumeralAdd]]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 8,modelNumeral M 11],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h8,h11]
theorem rootTo2 (k tail : M) :
    let t := F ones ![k,tail]
    let w := F ones ![k+1,tail]
    let r0 := (w+w)+(w+w)
    let r1 := r0+r0+1
    let r2 := r1+r1+1
    let r3 := r2+r2
    let r4 := r3+r3+1
    let r5 := r4+r4
    let r6 := r5+r5
    let r7 := r6+r6
    let r8 := r7+r7+1
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let b := (a4+a4)+(a4+a4)+1
    let c := b+b+1
    let d := c+c
    F PA194Stepper.stepper ![modelNumeral M 19,F pairCode ![modelNumeral M 24,
      F pairCode ![(1 : M),r8]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![(d+d)+(d+d),t]] := by
  dsimp only
  let t := F ones ![k,tail]
  have hw : F ones ![k+1,tail] = t+t+1 := by
    change F ones ![F addCode ![k,F oneCode Fin.elim0],tail] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hw]
  exact nineteenTo2 (1 : M) t
#print axioms rootTo2
#print axioms nineteenTo2
#print axioms elevenTo2
end models
end PA194Site29ThirdDispatch
