import PA194Site32ZeroHeaderTo16
import PA194Site32SecondReturn
import PA194Site27ZeroTo24
import PA194HeaderController
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroReturnFrom16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ZeroRuns PA194HeaderController PA194Site28SecondReturn PA194Site32SecondReturn PA194Site27ZeroTo24 PA194SeedHeaderTo21 PA194FiniteControls PA194StateOne BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem returnTo24 (r : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let s := (1+1)+(r+r)+(r+r)
    let b := (s+s)+(s+s)+1
    let c := ((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 6,c],
      F pairCode ![modelNumeral M 16,F pairCode ![a1,s]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),b]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let u := (1 : M)+r+r
  let s := u+u
  let b := (s+s)+(s+s)+1
  let c := b+b+1
  let heven16 := rowEvenLeft (M := M) 16 17 (by decide) (by decide +kernel)
  let heven17 := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  have h6 : F PA194Stepper.stepper ![modelNumeral M 6,F pairCode ![modelNumeral M 16,F pairCode ![a0+a0,s]]] =
      F pairCode ![modelNumeral M 18,F pairCode ![(0 : M),((c+c)+(c+c))+((c+c)+(c+c))]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 5),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 5 = F Code.succ (fun _ => modelNumeral M 4) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
    rw [heven16]
    have h17 := seventeenZeroOddLeft (M := M) (1 : M) s
    change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![a0,(s+s)]]) = _ at h17
    rw [h17]
    have h18 := eighteenOneOddLeft (M := M) (0 : M) (s+s)
    simp only [zero_add,add_zero] at h18
    change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![(1 : M),b]]) = _ at h18
    rw [h18]
    have h16 := oneFrom16 (M := M) (0 : M) b
    simp only [zero_add,add_zero] at h16
    change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![(0 : M),c]]) = _ at h16
    have h16z := heven16 (0 : M) c
    have h17z := heven17 (0 : M) (c+c)
    simp only [zero_add] at h16z h17z
    rw [h16,h16z,h17z]
  have hhead := headerHandoff (modelNumeral M 2) (0 : M) b
  dsimp only at hhead
  have hz : F zeros ![modelNumeral M 6,(0 : M)] = (0 : M) := by
    rw [←PA194HeaderController.zerosSix]
    simp only [zero_add]
  simp only [PA194HeaderController.zerosTwo,hz,zero_add,add_zero] at hhead
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 6,_],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  have heq : (1+1)+(r+r)+(r+r) = s := by dsimp only [s,u]; simp only [add_assoc,add_comm,add_left_comm]
  rw [heq,h6,hhead]
#print axioms returnTo24
end models
end PA194Site32ZeroReturnFrom16
