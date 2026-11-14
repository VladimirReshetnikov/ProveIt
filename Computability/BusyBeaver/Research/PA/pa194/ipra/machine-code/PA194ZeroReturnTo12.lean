import PA194RollbackCell
import PA194DecrementZeroCell
import PA194SeedHeaderTo21
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroReturnTo12
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RollbackCell PA194DecrementZeroCell PA194SeedHeaderTo21
open PA194RightRows PA194BinaryDouble PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem fourTo12 (j w : M) :
    let a0 := j+j
    let a1 := a0+a0
    let a2 := a1+a1
    let p := w+w+1
    let p1 := p+p
    let p2 := p1+p1
    F PA194Stepper.stepper ![modelNumeral M 4,F pairCode ![modelNumeral M 11,F pairCode ![a2,w+w]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,p2]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := j+j
  let a1 := a0+a0
  let p := w+w+1
  have h11 := packedEleven (a1+a1) w
  rw [(modelDouble a1).1,(modelDouble a1).2,zero_add] at h11
  have h11' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 11,F pairCode ![a1+a1,w+w]]) =
      F pairCode ![modelNumeral M 8,F pairCode ![a1,p+p]] := by
    convert h11 using 1 <;> dsimp [p] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h8 := rowEvenLeft (M := M) 8 10 (by decide) (by decide +kernel)
  have h10 := rowEvenLeft (M := M) 10 9 (by decide) (by decide +kernel)
  have h9 := rightZero (M := M) 9 1 12 (by decide) (by decide +kernel)
  simp only [show modelNumeral M 1 = (1 : M) from PA194StateOne.modelNumeralOne] at h9
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 3),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h11',h8,h10,h9]
theorem returnTo12 (k j out : M) :
    let j1 := j+j
    let j2 := j1+j1
    let j3 := j2+j2
    let j4 := j3+j3
    let scan := F ones ![k,j4]
    let a := scan+scan+1
    let u := out+out+1
    let r := u+u
    let w := F ones ![k+1,r]
    let p := w+w+1
    let p1 := p+p
    let p2 := p1+p1
    F PA194Stepper.stepper ![(modelNumeral M 2+(k+1))+modelNumeral M 4,
      F pairCode ![modelNumeral M 11,F pairCode ![a+a+1,out+out]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![j+j+1,p2]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let j1 := j+j
  let j2 := j1+j1
  let j3 := j2+j2
  let j4 := j3+j3
  let scan := F ones ![k,j4]
  let a := scan+scan+1
  let u := out+out+1
  let r := u+u
  let w := F ones ![k+1,r]
  have hafter := modelAfterBoundary a out
  dsimp only at hafter
  rw [(modelOdd scan).1,(modelOdd scan).2] at hafter
  have hr : (1 : M)+(u+u)+(u+u) = r+r+1 := by
    dsimp [r]; simp only [add_assoc,add_comm,add_left_comm]
  rw [hr] at hafter
  have hrollback := modelRollbackBoundary k j3 r
  have h4 := fourTo12 j w
  dsimp only at h4
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2+(k+1),modelNumeral M 4],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![modelNumeral M 4,F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,k+1],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,hafter,hrollback,h4]
#print axioms returnTo12
#print axioms fourTo12
end models
end PA194ZeroReturnTo12
