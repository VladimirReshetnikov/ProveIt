import PA194Site32ZeroRollback
import PA194RollbackCell
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroToBoundary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194RollbackCell
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194Site32ZeroRollback
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroToBoundary (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let l := (a6+a6)+(a6+a6)
    let w := F ones ![k+1,F sourceFileCode args]
    ∃ clock : M, F PA194Stepper.stepper ![clock,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 11,F pairCode ![l,w+w]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  let l := (a6+a6)+(a6+a6)
  let scan := F ones ![k,l+l]
  let f := F sourceFileCode args
  let w := F ones ![k+1,f]
  have hb : before k = scan+scan+1 := by
    dsimp only [before,scan,l,a6,a5,a4,a3,a2,a1,a0]
    change F ones ![F addCode ![k,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  obtain ⟨c,h⟩ := PA194Site32ZeroRollback.zeroRollback k args hz
  rw [hb,(modelOdd scan).1,(modelOdd scan).2] at h
  have hstart : F PA194Stepper.stepper ![c,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 11,F pairCode ![scan,f+f+1]] := by
    convert h using 1 <;> simp only [f,add_assoc,add_comm,add_left_comm]
  have hr := PA194RollbackCell.modelRollbackBoundary k l f
  change F PA194Stepper.stepper ![k+1,F pairCode ![modelNumeral M 11,F pairCode ![scan,f+f+1]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![l,w+w]] at hr
  refine ⟨F addCode ![c,k+1],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,hstart,hr]
#print axioms zeroToBoundary
end models
end PA194Site32ZeroToBoundary
