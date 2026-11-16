import PA194Site32ZeroTo14
import PA194Site32ZeroHeaderTo16
import PA194Site32ZeroReturnFrom16
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroTo24
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

theorem zeroTo24 (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let f := F sourceFileCode args
    let n := (((k+1)+1)+1)+1
    let z := F zeros ![n,(1 : M)+f+f]
    let r := (z+z)+(z+z)
    let s := (1+1)+(r+r)+(r+r)
    let b := (s+s)+(s+s)+1
    ∃ clock : M, F PA194Stepper.stepper ![clock,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),b]] := by
  dsimp only
  let v := physicalArgs args
  let f := F sourceFileCode args
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  have hf : f = p+p := by rw [show f = F (fileCode 10) v from modelSourceFile args,modelFileSucc,modelBlock]
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let n := (((k+1)+1)+1)+1
  let z := F zeros ![n,(1 : M)+f+f]
  let r := (z+z)+(z+z)
  let c16 := ((1 : M)+n)+modelNumeral M 3
  let rc := ((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1
  obtain ⟨clock,h14⟩ := PA194Site32ZeroTo14.zeroTo14 k args hz
  have h16 := PA194Site32ZeroHeaderTo16.from14To16 k a2 p
  dsimp only at h16
  rw [←hf,(modelDouble a1).1,(modelDouble a1).2,zero_add] at h16
  have h24 := PA194Site32ZeroReturnFrom16.returnTo24 r
  dsimp only at h24
  have hmid : F PA194Stepper.stepper ![F addCode ![clock,c16],PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![a1,(1+1)+(r+r)+(r+r)]] := by
    rw [PA194StepperCompose.modelStepperCompose,h14,h16]
  refine ⟨F addCode ![F addCode ![clock,c16],F addCode ![modelNumeral M 6,rc]],?_⟩
  rw [PA194StepperCompose.modelStepperCompose,hmid,h24]
#print axioms zeroTo24
end models
end PA194Site32ZeroTo24
