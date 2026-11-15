import PA194Site32PositiveTo12Exact
import PA194ThirteenExitComposition
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32PositiveTo14Exact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194OnesCommute PA194HeaderController
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

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  F addCode ![PA194Site32PositiveTo12Exact.clock k args,((modelNumeral M 2+1)+(k+1))+1]

theorem positiveTo14 (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let l := a6+a6+1
    let l' := F zeros ![k+1,F zeros ![modelNumeral M 2,l]+F zeros ![modelNumeral M 2,l]]
    let f := F sourceFileCode (Function.update args 6 m)
    F PA194Stepper.stepper ![clock k args,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => l'),F parityCode (fun _ => l')+f+f]] := by
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
  let l := a6+a6+1
  have h12 := PA194Site32PositiveTo12Exact.positiveTo12 k m args hm
  dsimp only at h12
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 2) (k+1) l p
  rw [←hf,zerosTwo] at hs
  have heq : (1 : M)+f+f = f+f+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [heq,modelOnesCommute] at h12
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h12,hs]
#print axioms positiveTo14
end models
end PA194Site32PositiveTo14Exact
