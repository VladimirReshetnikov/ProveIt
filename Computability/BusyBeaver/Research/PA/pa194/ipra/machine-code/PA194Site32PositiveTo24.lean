import PA194Site32PositiveTo14
import PA194ZeroReturnTo16
import PA194Site32PositiveReturnFrom16
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32PositiveTo24
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

theorem positiveTo24 (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    let f := F sourceFileCode (Function.update args 6 m)
    let z := F zeros ![k+1,(1 : M)+f+f]
    let r := (z+z)+(z+z)
    let r1 := (1 : M)+r+r
    let r2 := r1+r1+1
    let r3 := r2+r2+1
    let t := (1 : M)+r3+r3
    let t1 := t+t
    let t2 := t1+t1
    let t3 := t2+t2
    let t4 := t3+t3
    ∃ clock : M, F PA194Stepper.stepper ![clock,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),t4+1]] := by
  dsimp only
  let updated := Function.update args 6 m
  let v := physicalArgs updated
  let f := F sourceFileCode updated
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  have hf : f=p+p := by rw [show f = F (fileCode 10) v from modelSourceFile updated,modelFileSucc,modelBlock]
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  let z := F zeros ![k+1,(1 : M)+f+f]
  let r := (z+z)+(z+z)
  let c16 := ((1 : M)+(k+1))+modelNumeral M 3
  let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
  obtain ⟨clock,h14⟩ := PA194Site32PositiveTo14.positiveTo14 k m args hm
  have h16 := PA194ZeroReturnTo16.from14To16 k a6 p
  dsimp only at h16
  rw [←hf,(modelOdd a5).1,(modelOdd a5).2] at h16
  have h24 := PA194Site32PositiveReturnFrom16.returnTo24 r
  dsimp only at h24
  have hmid : F PA194Stepper.stepper ![F addCode ![clock,c16],PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![a5,(1 : M)+(1+1)+(r+r)+(r+r)]] := by
    rw [PA194StepperCompose.modelStepperCompose,h14,h16]
  refine ⟨F addCode ![F addCode ![clock,c16],F addCode ![modelNumeral M 3,modelNumeral M 3+rc]],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,hmid,h24]
#print axioms positiveTo24
end models
end PA194Site32PositiveTo24
