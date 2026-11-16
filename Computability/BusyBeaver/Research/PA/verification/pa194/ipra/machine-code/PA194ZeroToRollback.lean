import PA194RollbackEvenTail
import PA194RollbackCell
import PA194DecrementZeroCell
import PA194LeftOneWriteOne
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroToRollback
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RollbackEvenTail PA194RollbackCell PA194DecrementZeroCell
open PA194LeftOneWriteOne PA194BinaryDouble PA194UnaryRuns PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem fiveTo11 (a r : M) :
    let p := r+r+1
    let d := a+a+1
    let z := d+d
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 5,F pairCode ![z+z+1,p]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![d,(p+p)+(p+p)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let p := r+r+1
  let d := a+a+1
  let z := d+d
  have h5 := leftOneWriteOne 5 8 (by decide) (by decide +kernel) (z+z+1) r
  rw [(modelOdd z).1,(modelOdd z).2] at h5
  have hr : (1 : M)+(1+1)+(r+r)+(r+r) = p+p+1 := by dsimp [p]; simp only [add_assoc,add_comm,add_left_comm]
  rw [hr] at h5
  have h8 := packedEight z p
  rw [(modelDouble d).1,(modelDouble d).2,zero_add] at h8
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
      PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
      PA194Stepper.modelStepperZero,h5,h8]

theorem zeroToRollback (n l r : M) :
    let a := F ones ![n,l+l]
    let d := a+a+1
    let z := d+d
    let p := r+r+1
    let u := p+p
    let file := (u+u+1)+(u+u+1)
    let out := F ones ![n,file]
    F PA194Stepper.stepper ![(modelNumeral M 2+modelNumeral M 2)+n,
      F pairCode ![modelNumeral M 5,F pairCode ![z+z+1,p]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![l,out+out]] := by
  dsimp only
  let a := F ones ![n,l+l]
  let p := r+r+1
  let u := p+p
  let file := (u+u+1)+(u+u+1)
  have h5 := fiveTo11 a r
  dsimp only at h5
  have h11 := modelAfterBoundary a u
  dsimp only at h11
  have hroll := rollbackEven n l file
  dsimp only at hroll
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 2+modelNumeral M 2,n],_] = _
  rw [PA194StepperCompose.modelStepperCompose]
  change F PA194Stepper.stepper ![n,F PA194Stepper.stepper ![F addCode ![modelNumeral M 2,modelNumeral M 2],_]] = _
  rw [PA194StepperCompose.modelStepperCompose,h5,h11,hroll]
#print axioms fiveTo11
#print axioms zeroToRollback
end models
end PA194ZeroToRollback
