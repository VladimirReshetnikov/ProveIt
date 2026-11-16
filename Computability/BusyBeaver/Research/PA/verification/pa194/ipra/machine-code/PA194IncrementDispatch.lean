import PA194RightRows
import PA194HeaderController
/-! The nine-bit controller path from dense state 24 to the marked increment entry. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PA194IncrementDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194MarkerReturnCell PA194ZeroRuns PA194BinaryDouble PA194RightRows PA194HeaderController TableDispatch PA194StateOne
open PackedIterationModel ConfigurationStep PRAModelIOpenPairing PA194ControllerReturn PA194OnesCommute
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row24 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 24 1 26 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row26 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 29,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 26 0 29 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row29 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 34,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 29 0 34 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row34 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 34,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 45,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 34 1 45 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row45 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 45,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 64,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 45 1 64 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row64 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 64,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 90,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 64 1 90 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row90 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 90,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 109,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 90 0 109 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row109 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 109,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 70,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 109 0 70 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem row70 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 70,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 70 0 2 (by decide) (by decide +kernel) l r
  simpa only [modelNumeralOne, show modelNumeral M 0 = (0 : M) from rfl, add_zero] using h

theorem nineSteps (l r : M) :
    let t0 := r+r+1
    let t1 := t0+t0
    let t2 := t1+t1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let t5 := t4+t4+1
    let t6 := t5+t5
    let t7 := t6+t6
    let t8 := t7+t7+1
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2+1
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5
    let a7 := a6+a6
    let a8 := a7+a7
    F PA194Stepper.stepper ![modelNumeral M 9,F pairCode ![modelNumeral M 24,F pairCode ![l,t8]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![a8,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 8),_] = _
  rw [PA194Stepper.modelStepperSucc,
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
  rw [row24,row26,row29,row34,row45,row64,row90,row109,row70]
  congr 2 <;> ac_rfl
theorem onesOne (x : M) : F ones ![modelNumeral M 1,x] = x+x+1 := by
  change F ones ![F Code.succ (fun _ => modelNumeral M 0),x] = _
  rw [modelOnesSucc]
  change F ones ![(0 : M),x]+F ones ![(0 : M),x]+1 = _
  rw [modelOnesZero]

/-- The literal marker exits reach the marked-increment entry on a specified
nine-bit controller prefix, preserving the arbitrary residual right tape. -/
theorem markerToIncrement (i : Fin 2) (u r : M) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let t0 := r+r+1
    let t1 := t0+t0
    let t2 := t1+t1
    let t3 := t2+t2+1
    let t4 := t3+t3+1
    let t5 := t4+t4+1
    let t6 := t5+t5
    let t7 := t6+t6
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
    F PA194Stepper.stepper ![headerClock+modelNumeral M 9,
      F pairCode ![modelNumeral M (returnControl i),F pairCode ![((l+l)+(l+l))+((l+l)+(l+l))+1,t7+t7+1]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![a8,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let t0 := r+r+1
  let t1 := t0+t0
  let t2 := t1+t1
  let t3 := t2+t2+1
  let t4 := t3+t3+1
  let t5 := t4+t4+1
  let t6 := t5+t5
  let t7 := t6+t6
  let g := F zeros ![modelNumeral M 2,F zeros ![modelNumeral M 6,u]]
  let h := g+g+1
  have hm := markerTo24 i (modelNumeral M 1) u t7
  dsimp only at hm
  simp only [onesOne] at hm
  have hn := nineSteps h r
  dsimp only at hn
  change F PA194Stepper.stepper ![F addCode ![(((modelNumeral M 1+1)+1)+1)+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1),modelNumeral M 9],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm,hn]
#print axioms markerToIncrement
#print axioms nineSteps
end models
end PA194IncrementDispatch
