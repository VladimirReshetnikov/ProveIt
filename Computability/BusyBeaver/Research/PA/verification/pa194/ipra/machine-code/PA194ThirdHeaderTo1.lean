import PA194SeedHeaderPass
import PA194SeedHeaderDispatch
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ThirdHeaderTo1
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderDispatch PA194IncrementDispatch PA194RightRows
open PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row59one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 59,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 1,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 59 0 1 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem twelveSteps (l r : M) :
    let s := r+r+1
    let y0 := s
    let y1 := y0+y0
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let y5 := y4+y4
    let y6 := y5+y5
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3
    let a5 := a4+a4
    F PA194Stepper.stepper ![modelNumeral M 12,F pairCode ![modelNumeral M 24,F pairCode ![l,y6+y6+1]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(a5+a5)+(a5+a5),r]] := by
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 11),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 11 = F Code.succ (fun _ => modelNumeral M 10) from rfl,
      PA194Stepper.modelStepperSucc,
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
      PA194Stepper.modelStepperZero]
  rw [row24,row26,row29,row34zero,row44zero,row62zero,row87zero,row46zero,row65zero,row91zero,row110zero,row59one]
  rfl

#print axioms twelveSteps
end models
end PA194ThirdHeaderTo1
