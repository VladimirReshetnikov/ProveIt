import PA194State18To24
import PA194GenericZeroRightScan
import PA194StepperCompose
import PA194ControllerReturn
/-! An all-model controller segment from either marker exit to dense state 24. -/
set_option autoImplicit false
namespace PA194HeaderController
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194MarkerReturnCell PA194ZeroRuns PA194BinaryDouble PA194State18To24 PA194GenericZeroRightScan
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

theorem packed18 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 18,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 19,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 18,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 18,l,r+r],F nextL ![TableDispatch.modelNumeral M 18,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 18,l,r+r]) = stepSem (TableDispatch.modelNumeral M 18) l (r+r) at hm
  rw [←hm,modelState18Even]

theorem packed19 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 19,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 20,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 19,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 19,l,r+r],F nextL ![TableDispatch.modelNumeral M 19,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 19,l,r+r]) = stepSem (TableDispatch.modelNumeral M 19) l (r+r) at hm
  rw [←hm,modelState19Even]

theorem packed20 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 20,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 21,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 20,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 20,l,r+r],F nextL ![TableDispatch.modelNumeral M 20,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 20,l,r+r]) = stepSem (TableDispatch.modelNumeral M 20) l (r+r) at hm
  rw [←hm,modelState20Even]

theorem packed21 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 21,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 22,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 21,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 21,l,r+r],F nextL ![TableDispatch.modelNumeral M 21,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 21,l,r+r]) = stepSem (TableDispatch.modelNumeral M 21) l (r+r) at hm
  rw [←hm,modelState21Even]

theorem packed22 (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 22,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 23,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 22,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 22,l,r+r],F nextL ![TableDispatch.modelNumeral M 22,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 22,l,r+r]) = stepSem (TableDispatch.modelNumeral M 22) l (r+r) at hm
  rw [←hm,modelState22Even]

theorem packed23Even (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 23,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 23,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 23,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 23,l,r+r],F nextL ![TableDispatch.modelNumeral M 23,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 23,l,r+r]) = stepSem (TableDispatch.modelNumeral M 23) l (r+r) at hm
  rw [←hm,modelState23Even]

theorem packed23Odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 23,F pairCode ![l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 23,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 23,l,r+r+1],F nextL ![TableDispatch.modelNumeral M 23,l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 23,l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 23) l (r+r+1) at hm
  rw [←hm,modelState23Odd]

theorem scan23 (n l r : M) :
    F PA194Stepper.stepper ![n,F pairCode ![TableDispatch.modelNumeral M 23,F pairCode ![l,F zeros ![n,r]]]] =
    F pairCode ![TableDispatch.modelNumeral M 23,F pairCode ![F zeros ![n,l],r]] := by
  exact PA194GenericZeroRightScan.modelFullScan 23 packed23Even n l r
theorem walk18_23 (l r : M) :
    let z1 := l+l
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let a := r+r
    let b := a+a
    let c := b+b
    let d := c+c
    let e := d+d
    let f := e+e
    F PA194Stepper.stepper ![TableDispatch.modelNumeral M 5,
      F pairCode ![TableDispatch.modelNumeral M 18,F pairCode ![z4,a]]] =
    F pairCode ![TableDispatch.modelNumeral M 23,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+f]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  change F PA194Stepper.stepper ![F Code.succ (fun _ => TableDispatch.modelNumeral M 4),_] = _
  rw [PA194Stepper.modelStepperSucc]
  rw [show TableDispatch.modelNumeral M 4 = F Code.succ (fun _ => TableDispatch.modelNumeral M 3) from rfl,
      PA194Stepper.modelStepperSucc,
      show TableDispatch.modelNumeral M 3 = F Code.succ (fun _ => TableDispatch.modelNumeral M 2) from rfl,
      PA194Stepper.modelStepperSucc,
      show TableDispatch.modelNumeral M 2 = F Code.succ (fun _ => TableDispatch.modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show TableDispatch.modelNumeral M 1 = F Code.succ (fun _ => TableDispatch.modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show TableDispatch.modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero]
  rw [packed18]
  simp only [(modelDouble _).1,(modelDouble _).2,zero_add]
  rw [packed19]
  simp only [(modelDouble _).1,(modelDouble _).2,zero_add]
  rw [packed20]
  simp only [(modelDouble _).1,(modelDouble _).2,zero_add]
  rw [packed21]
  simp only [(modelDouble _).1,(modelDouble _).2,zero_add]
  rw [packed22]
  simp only [add_assoc]

theorem zerosSix (r : M) :
    let a := r+r
    let b := a+a
    let c := b+b
    let d := c+c
    let e := d+d
    e+e = F zeros ![TableDispatch.modelNumeral M 6,r] := by
  dsimp only
  rw [show TableDispatch.modelNumeral M 6 = F Code.succ (fun _ => TableDispatch.modelNumeral M 5) from rfl,
      modelZerosSucc,
      show TableDispatch.modelNumeral M 5 = F Code.succ (fun _ => TableDispatch.modelNumeral M 4) from rfl,
      modelZerosSucc,
      show TableDispatch.modelNumeral M 4 = F Code.succ (fun _ => TableDispatch.modelNumeral M 3) from rfl,
      modelZerosSucc,
      show TableDispatch.modelNumeral M 3 = F Code.succ (fun _ => TableDispatch.modelNumeral M 2) from rfl,
      modelZerosSucc,
      show TableDispatch.modelNumeral M 2 = F Code.succ (fun _ => TableDispatch.modelNumeral M 1) from rfl,
      modelZerosSucc,
      show TableDispatch.modelNumeral M 1 = F Code.succ (fun _ => TableDispatch.modelNumeral M 0) from rfl,
      modelZerosSucc]
  rw [show TableDispatch.modelNumeral M 0 = (0 : M) from rfl]
  simp only [modelZerosZero]
/-- From dense state 18, a zero under the head, five zero cells on the left,
then a model-length run of zeros followed by a one on the right, reach state 24.
The theorem exposes the exact binary tape halves and clock; it is a controller
segment and does not assert a source instruction is simulated. -/
theorem headerHandoff (n u t : M) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let r := F zeros ![n,t+t+1]
    let l := F zeros ![n,F zeros ![TableDispatch.modelNumeral M 6,u]]
    F PA194Stepper.stepper ![((TableDispatch.modelNumeral M 5+TableDispatch.modelNumeral M 6)+n)+1,
      F pairCode ![TableDispatch.modelNumeral M 18,F pairCode ![z4,r+r]]] =
    F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![l+l+1,t]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let r := F zeros ![n,t+t+1]
  have hw := walk18_23 (u+u) r
  dsimp only at hw
  rw [(modelDouble u).1,(modelDouble u).2,zero_add] at hw
  rw [zerosSix r] at hw
  change F PA194Stepper.stepper ![F addCode ![(TableDispatch.modelNumeral M 5+TableDispatch.modelNumeral M 6)+n,F oneCode Fin.elim0],_] = _
  rw [modelAddOne,PA194Stepper.modelStepperSucc]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![F addCode ![TableDispatch.modelNumeral M 5+TableDispatch.modelNumeral M 6,n],_]) = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![n,F PA194Stepper.stepper ![F addCode ![TableDispatch.modelNumeral M 5,TableDispatch.modelNumeral M 6],_]]) = _
  rw [PA194StepperCompose.modelStepperCompose,hw,scan23,scan23,packed23Odd]
theorem zerosTwo (r : M) : F zeros ![TableDispatch.modelNumeral M 2,r] = (r+r)+(r+r) := by
  rw [show TableDispatch.modelNumeral M 2 = F Code.succ (fun _ => TableDispatch.modelNumeral M 1) from rfl,
      modelZerosSucc,
      show TableDispatch.modelNumeral M 1 = F Code.succ (fun _ => TableDispatch.modelNumeral M 0) from rfl,
      modelZerosSucc,
      show TableDispatch.modelNumeral M 0 = (0 : M) from rfl]
  simp only [modelZerosZero]

/-- For either marker-exit control, cross the one-run and padded header to
state 24. The input has left half `ones(k, 256*u)` and right half `2*t+1`;
the output has left half `512*u+1` and right half `ones(k,t)`. Every argument
may be nonstandard in the candidate-PRA model. The equation's explicit clock
is the sum of the marker return and header handoff clocks. -/
theorem markerTo24 (i : Fin 2) (k u t : M) :
    let z := u+u
    let z1 := z+z
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let l := z4+z4
    let v := F ones ![k,t]
    let y := F zeros ![TableDispatch.modelNumeral M 2,F zeros ![TableDispatch.modelNumeral M 6,u]]
    F PA194Stepper.stepper ![(((k+1)+1)+1)+(((TableDispatch.modelNumeral M 5+TableDispatch.modelNumeral M 6)+TableDispatch.modelNumeral M 2)+1),
      F pairCode ![TableDispatch.modelNumeral M (returnControl i),
        F pairCode ![F ones ![k,(l+l)+(l+l)],t+t+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 24,F pairCode ![y+y+1,v]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let z := u+u
  let z1 := z+z
  let z2 := z1+z1
  let z3 := z2+z2
  let z4 := z3+z3
  let l := z4+z4
  let v := F ones ![k,t]
  have hm := modelReturnToControl18 i k l t
  dsimp only at hm
  dsimp only [l] at hm
  rw [(modelDouble z4).1,(modelDouble z4).2,zero_add] at hm
  have ha : F ones ![k,(1 : M)+t+t] = v+v+1 := by
    simpa only [v, add_assoc, add_comm, add_left_comm] using modelOnesCommute k t
  rw [ha] at hm
  have hh := headerHandoff (TableDispatch.modelNumeral M 2) u v
  dsimp only at hh
  rw [zerosTwo] at hh
  change F PA194Stepper.stepper ![F addCode ![((k+1)+1)+1,((TableDispatch.modelNumeral M 5+TableDispatch.modelNumeral M 6)+TableDispatch.modelNumeral M 2)+1],_] = _
  rw [PA194StepperCompose.modelStepperCompose,hm]
  exact hh
#print axioms markerTo24
#print axioms headerHandoff
#print axioms zerosSix
#print axioms walk18_23
#print axioms scan23
end models
end PA194HeaderController
