import PA194SecondHeaderTo93
import PA194NinetyThreeReturnTwoWithTail
import PA194SeedHeaderTo22
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SecondHeaderPass
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SecondHeaderTo93 PA194NinetyThreeReturnTwoWithTail
open PA194SeedHeaderTo22 PA194BinaryDouble PA194RegisterFile PA194UnaryRuns
open PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem secondHeaderPass (n : Nat) (e : Fin (n+4) → M) (r : M)
    (hr : F (fileCode (n+3)) e = r+r) :
    let e1 : Fin (n+3) → M := fun i => e i.succ
    let e2 : Fin (n+2) → M := fun i => e1 i.succ
    let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
    let c := (b+b)+(b+b)
    let w1 := F ones ![e1 0,(1 : M)+c+c]
    let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
    let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
    let backClock := (e1 0+1)+((e 0+1)+1)
    let z0 := r+r+1
    let z1 := z0+z0
    let z2 := z1+z1
    let z3 := z2+z2
    let z4 := z3+z3
    let z5 := z4+z4
    let v1 := w2+w2
    let v2 := v1+v1
    let v3 := v2+v2
    let v4 := v3+v3
    let v5 := v4+v4
    let v6 := v5+v5
    let v7 := v6+v6
    let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((modelNumeral M 7+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 5)+returnClock,
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),z5+z5+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),v7+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3
  let a5 := a4+a4
  let e1 : Fin (n+3) → M := fun i => e i.succ
  let e2 : Fin (n+2) → M := fun i => e1 i.succ
  let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e1 0,(1 : M)+c+c]
  let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
  let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
  let backClock := (e1 0+1)+((e 0+1)+1)
  let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h93 := sevenTo93 (1 : M) r
  dsimp only at h93
  have h17 := ninetyThreeReturnTwoWithTailExact n e a5 r hr
  dsimp only at h17
  rw [(modelDouble a4).1,(modelDouble a4).2,zero_add] at h17
  have h22 := fiveSteps (1 : M) w2
  dsimp only at h22
  let v1 := w2+w2
  let v2 := v1+v1
  let v3 := v2+v2
  let v4 := v3+v3
  let v5 := v4+v4
  let v6 := v5+v5
  have h24 := PA194SeedHeaderReturn22.returnTo24 v6
  dsimp only at h24
  change F PA194Stepper.stepper ![F addCode ![((modelNumeral M 7+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 5),returnClock],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![returnClock,F PA194Stepper.stepper ![F addCode ![(modelNumeral M 7+((scanClock+modelNumeral M 3)+backClock)),modelNumeral M 5],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![returnClock,F PA194Stepper.stepper ![modelNumeral M 5,F PA194Stepper.stepper ![F addCode ![modelNumeral M 7,((scanClock+modelNumeral M 3)+backClock)],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose,h93,h17,h22,h24]
#print axioms secondHeaderPass
end models
end PA194SecondHeaderPass
