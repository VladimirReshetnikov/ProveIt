import PA194Site32ZeroTo12Exact
import PA194Site32ZeroTo12
import PA194ThirteenExitComposition
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroTo14Exact
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

theorem zerosFive (p : M) :
    let p1 := p+p
    let p2 := p1+p1
    let p3 := p2+p2
    let p4 := p3+p3
    F zeros ![modelNumeral M 5,p] = p4+p4 := by
  dsimp only
  change F zeros ![F Code.succ (fun _ => modelNumeral M 4),p] = _
  rw [modelZerosSucc,
    show modelNumeral M 4 = F Code.succ (fun _ => modelNumeral M 3) from rfl,modelZerosSucc,
    show modelNumeral M 3 = F Code.succ (fun _ => modelNumeral M 2) from rfl,modelZerosSucc,
    show modelNumeral M 2 = F Code.succ (fun _ => modelNumeral M 1) from rfl,modelZerosSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,modelZerosSucc,
    show modelNumeral M 0 = (0 : M) from rfl,modelZerosZero]

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  F addCode ![PA194Site32ZeroTo12Exact.clock k args,((modelNumeral M 5+1)+(k+1))+1]

theorem zeroTo14 (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let l := a3+1
    let l' := F zeros ![k+1,F zeros ![modelNumeral M 5,l]+F zeros ![modelNumeral M 5,l]]
    let f := F sourceFileCode args
    F PA194Stepper.stepper ![clock k args,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => l'),F parityCode (fun _ => l')+f+f]] := by
  dsimp only
  let v := physicalArgs args
  let p0 := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  have hf : F sourceFileCode args = p0+p0 := by
    rw [show F sourceFileCode args = F (fileCode 10) v from modelSourceFile args,modelFileSucc,modelBlock]
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let l := a3+1
  let w := F ones ![k+1,F sourceFileCode args]
  have h := PA194Site32ZeroTo12Exact.zeroTo12 k args hz
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 5) (k+1) l p0
  rw [←hf,zerosFive] at hs
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h,hs]
#print axioms zerosFive
#print axioms zeroTo14
end models
end PA194Site32ZeroTo14Exact
