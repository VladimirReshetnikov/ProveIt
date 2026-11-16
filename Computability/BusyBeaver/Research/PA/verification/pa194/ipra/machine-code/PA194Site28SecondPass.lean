import PA194Site28SecondDispatch
import PA194Site28SecondReturn
import PA194NinetyThreeReturnTwoWithTail
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28SecondPass
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28SecondDispatch PA194Site28SecondReturn PA194NinetyThreeReturnTwoWithTail PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls PA194StateOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem secondPass (n : Nat) (e : Fin (n+4) → M) (r : M)
    (hr : F (fileCode (n+3)) e = r+r) :
    let e1 : Fin (n+3) → M := fun i => e i.succ
    let e2 : Fin (n+2) → M := fun i => e1 i.succ
    let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
    let c := (b+b)+(b+b)
    let w1 := F ones ![e1 0,(1 : M)+c+c]
    let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
    let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
    let backClock := (e1 0+1)+((e 0+1)+1)
    let s := r+r+1
    let u0 := s+s
    let u1 := u0+u0+1
    let u2 := u1+u1
    let u3 := u2+u2+1
    let u4 := u3+u3
    let u5 := u4+u4
    let u6 := u5+u5
    let v1 := w2+w2
    let v2 := v1+v1
    let v3 := v2+v2
    let x0 := v3+1
    let x1 := x0+x0
    let x2 := x1+x1+1
    let x3 := x2+x2
    let x4 := x3+x3
    let x5 := x4+x4
    let x6 := x5+x5+1
    let returnClock := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![((modelNumeral M 9+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 7)+returnClock,
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),u6+u6+1]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),x6]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5+1
  let a7 := a6+a6
  let e1 : Fin (n+3) → M := fun i => e i.succ
  let e2 : Fin (n+2) → M := fun i => e1 i.succ
  let b := F ones ![e2 0,F (fileCode n) (fun i => e2 i.succ)]
  let c := (b+b)+(b+b)
  let w1 := F ones ![e1 0,(1 : M)+c+c]
  let w2 := F ones ![e 0,(1 : M)+(w1+w1)+(w1+w1)]
  let scanClock := ((e 0+1)+1)+((e1 0+1)+1)
  let backClock := (e1 0+1)+((e 0+1)+1)
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  let v1 := w2+w2
  let v2 := v1+v1
  let v3 := v2+v2
  let x0 := v3+1
  let x1 := x0+x0
  let x2 := x1+x1+1
  let x3 := x2+x2
  let x4 := x3+x3
  let x5 := x4+x4
  have h93 := nineTo93 (1 : M) r
  dsimp only at h93
  have h17 := ninetyThreeReturnTwoWithTailExact n e a7 r hr
  dsimp only at h17
  rw [(modelDouble a6).1,(modelDouble a6).2,zero_add] at h17
  have h19 := sevenTo19 (M := M) w2
  dsimp only at h19
  have h24 := PA194SeedHeaderReturn19.returnTo24 (M := M) x5
  dsimp only at h24
  change F PA194Stepper.stepper ![F addCode ![((modelNumeral M 9+((scanClock+modelNumeral M 3)+backClock))+modelNumeral M 7),rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![rc,F PA194Stepper.stepper ![F addCode ![(modelNumeral M 9+((scanClock+modelNumeral M 3)+backClock)),modelNumeral M 7],_]] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![rc,F PA194Stepper.stepper ![modelNumeral M 7,F PA194Stepper.stepper ![F addCode ![modelNumeral M 9,((scanClock+modelNumeral M 3)+backClock)],_]]] = _
  rw [PA194StepperCompose.modelStepperCompose,h93,h17,h19,h24]
#print axioms secondPass
end models
end PA194Site28SecondPass
