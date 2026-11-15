import PA194Site27ZeroTo12
import PA194ThirteenExitComposition
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroTo14
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194SourceSite25Physical PA194Site27ZeroRollback PA194ReturnFile
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem returnedEven (e : Fin 11 → M) : ∃ r : M, returned e = r+r := by
  unfold returned
  rw [modelReturnCodeSucc]
  exact ⟨_,rfl⟩

theorem zeroTo14 (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M)) :
    ∃ r clock : M, returned e = r+r ∧
      let a0 := (1 : M)+(1 : M)+1
      let a1 := a0+a0
      let a2 := a1+a1
      let a3 := a2+a2
      let a4 := a3+a3+1
      let l := a4+a4+1
      let l' := F zeros ![k+1,F zeros ![modelNumeral M 2,l]+F zeros ![modelNumeral M 2,l]]
      F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
        F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => l'),F parityCode (fun _ => l')+(r+r)+(r+r)]] := by
  obtain ⟨r,hr⟩ := returnedEven e
  obtain ⟨c,h⟩ := PA194Site27ZeroTo12.zeroTo12 k e hz
  refine ⟨r,F addCode ![c,((modelNumeral M 2+1)+(k+1))+1],hr,?_⟩
  dsimp only
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let l := a4+a4+1
  let w := F ones ![k+1,r+r]
  rw [hr] at h
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 2) (k+1) l r
  rw [PA194HeaderController.zerosTwo] at hs
  rw [PA194StepperCompose.modelStepperCompose,h,hs]
#print axioms returnedEven
#print axioms zeroTo14
end models
end PA194Site27ZeroTo14
