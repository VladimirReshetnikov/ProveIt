import PA194Site32PositiveReturned
import PA194Site27PositiveHeaderTo12
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32PositiveTo12
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

theorem positiveTo12 (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let a5 := a4+a4+1
    let a6 := a5+a5+1
    let f := F sourceFileCode (Function.update args 6 m)
    let w := F ones ![k+1,(1 : M)+f+f]
    ∃ clock : M, F PA194Stepper.stepper ![clock,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 12,F pairCode ![a6+a6+1,(w+w)+(w+w)]] := by
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let a6 := a5+a5+1
  let updated := Function.update args 6 m
  let v := physicalArgs updated
  let f := F sourceFileCode updated
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  have hf : f = p+p := by rw [show f = F (fileCode 10) v from modelSourceFile updated,modelFileSucc,modelBlock]
  obtain ⟨clock,h⟩ := PA194Site32PositiveReturned.positiveReturned k m args hm
  have h12 := PA194Site27PositiveHeaderTo12.headerTo12 k a6 p
  dsimp only at h12
  rw [←hf] at h12
  change F PA194Stepper.stepper ![((1 : M)+((k+1)+1))+modelNumeral M 3,
    F pairCode ![modelNumeral M 6,F pairCode ![before k+before k+1,f]]] = _ at h12
  have hsum : (1 : M)+f+f = (f+f)+1 := by simp only [add_assoc,add_comm,add_left_comm]
  rw [hsum]
  refine ⟨F addCode ![clock,((1 : M)+((k+1)+1))+modelNumeral M 3],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,h,h12]
#print axioms positiveTo12
end models
end PA194Site32PositiveTo12
