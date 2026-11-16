import PA194Site31SecondTo17
import PA194SixteenScanInvariant
import PA194SixteenExitComposition
import PA194ZeroReturnFrom16
import PA194LeftOneWriteOne
import PA194LeftRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site31SecondReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SeedHeaderTo21 PA194LeftOneWriteOne PA194LeftRows PA194ZeroReturnFrom16 PA194SixteenExitComposition PA194BinaryDouble PA194UnaryRuns BinaryTapeCodes PRAModelIOpenPairing PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem return17To24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let w1 := w+w
    let w2 := w1+w1
    let w3 := w2+w2
    let u := (1 : M)+w3
    let t := (1 : M)+u+u
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 3+(modelNumeral M 3+rc),
      F pairCode ![modelNumeral M 17,F pairCode ![a5,w2]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let w1 := w+w
  let w2 := w1+w1
  let w3 := w2+w2
  let u := (1 : M)+w3
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  have h17 := leftZero 17 18 (by decide) (by decide +kernel) a5 w1
  rw [(modelOdd a4).1,(modelOdd a4).2] at h17
  have h17' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![a5,w2]]) =
      F pairCode ![modelNumeral M 18,F pairCode ![a4,w3+1]] := by
    convert h17 using 1 <;> dsimp only [w3,w2] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h18 := leftOneWriteOne 18 16 (by decide) (by decide +kernel) a4 w2
  rw [(modelOdd a3).1,(modelOdd a3).2] at h18
  have h18' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![a4,w3+1]]) =
      F pairCode ![modelNumeral M 16,F pairCode ![a3,u+u+1]] := by
    convert h18 using 1 <;> dsimp only [u,w3,w2] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h16 := leftOneWriteOne 16 16 (by decide) (by decide +kernel) a3 u
  rw [(modelDouble a2).1,(modelDouble a2).2,zero_add] at h16
  have h3 : F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 17,F pairCode ![a5,w2]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(u+u)+(u+u)]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h17',h18',h16]
  have hr := PA194ZeroReturnFrom16.returnFrom16 u
  dsimp only at hr
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,modelNumeral M 3+rc],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h3,hr]
#print axioms return17To24
end models
end PA194Site31SecondReturn
