import PA194SeedHeaderReturn20
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194PositiveReturnFrom16
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo21 PA194SeedHeaderReturn20 PA194LeftRows PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem row19Odd (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![l+l+1,r+r]]) =
    F pairCode ![modelNumeral M 20,F pairCode ![l,((r+r)+(r+r))+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := leftZero 19 20 (by decide) (by decide +kernel) (l+l+1) r
  rw [(modelOdd l).1,(modelOdd l).2] at h
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem returnFrom16 (r : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let t := (1 : M)+r+r
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
  let t4 := t3+t3
    let t4 := t3+t3
    let t5 := t4+t4
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 4+rc,F pairCode ![modelNumeral M 16,
      F pairCode ![a3,(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t5+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let t := (1 : M)+r+r
  let t1 := t+t
  let t2 := t1+t1
  let t3 := t2+t2
  let t4 := t3+t3
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h16 := rowEvenLeft (M := M) 16 17 (by decide) (by decide +kernel)
  have h17 := rowEvenLeft (M := M) 17 18 (by decide) (by decide +kernel)
  have h18 := rowEvenLeft (M := M) 18 19 (by decide) (by decide +kernel)
  have h4 : F PA194Stepper.stepper ![modelNumeral M 4,F pairCode ![modelNumeral M 16,
      F pairCode ![(((1 : M)+1+1+((1 : M)+1+1))+((1 : M)+1+1+((1 : M)+1+1)))+(((1 : M)+1+1+((1 : M)+1+1))+((1 : M)+1+1+((1 : M)+1+1))),t+t]]] =
      F pairCode ![modelNumeral M 20,F pairCode ![(1 : M),(t4+t4)+1]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 3),_] = _
    rw [PA194Stepper.modelStepperSucc,
        show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,
        PA194Stepper.modelStepperSucc,
        show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
        PA194Stepper.modelStepperSucc,
        show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
        PA194Stepper.modelStepperSucc,
        show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
        PA194Stepper.modelStepperZero,h16,h17,h18]
    have h19 := row19Odd (1 : M) t3
    rw [h19]
  have hr := PA194SeedHeaderReturn20.returnTo24 t4
  dsimp only at hr
  have ht : (1 : M)+1+(r+r)+(r+r) = t+t := by dsimp [t]; simp only [add_assoc,add_comm,add_left_comm]
  rw [ht]
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 4,rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h4,hr]
#print axioms returnFrom16
end models
end PA194PositiveReturnFrom16
