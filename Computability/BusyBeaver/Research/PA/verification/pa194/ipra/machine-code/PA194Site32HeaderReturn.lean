import PA194Site32HeaderTo17
import PA194ZeroReturnFrom16
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32HeaderReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site32HeaderTo17 PA194ZeroReturnFrom16 PA194LeftOneWriteOne PA194BinaryDouble PA194FiniteControls PA194StateOne PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem returnTo24 (w : M) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let r := (1 : M)+(w+w)+(w+w)
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![F addCode ![modelNumeral M 3,modelNumeral M 3+rc],
      F pairCode ![modelNumeral M 17,F pairCode ![a5,r]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 32) w]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let r := (1 : M)+(w+w)+(w+w)
  let rr := r+r+1
  have h17 := PA194LeftOneWriteOne.leftOneWriteOne 17 16 (by decide) (by decide +kernel) a5 (w+w)
  rw [(modelOdd a4).1,(modelOdd a4).2] at h17
  have h17' : F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![a5,r]]) =
      F pairCode ![modelNumeral M 16,F pairCode ![a4,rr]] := by
    convert h17 using 1 <;> dsimp only [r,rr] <;> simp only [add_assoc,add_comm,add_left_comm]
  have h16a := PA194LeftOneWriteOne.leftOneWriteOne 16 16 (by decide) (by decide +kernel) a4 r
  rw [(modelOdd a3).1,(modelOdd a3).2] at h16a
  have h16b := PA194LeftOneWriteOne.leftOneWriteOne 16 16 (by decide) (by decide +kernel) a3 rr
  rw [(modelDouble a2).1,(modelDouble a2).2,zero_add] at h16b
  have hrr : (1 : M)+(1+1)+(r+r)+(r+r) = rr+rr+1 := by
    dsimp only [rr]
    ac_rfl
  have h3 : F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 17,F pairCode ![a5,r]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![a2,(1+1)+(rr+rr)+(rr+rr)]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 2),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h17',h16a,hrr,h16b]
  have hr := PA194ZeroReturnFrom16.returnFrom16 rr
  dsimp only at hr
  rw [PA194StepperCompose.modelStepperCompose,h3,hr]
  rw [PA194Path32Header.path32]
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  dsimp only [rr,r]
  simp only [add_assoc,add_comm,add_left_comm]
#print axioms returnTo24
end models
end PA194Site32HeaderReturn
