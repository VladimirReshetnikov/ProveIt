import PA194Site32ZeroToBoundaryExact
import PA194Site32ZeroToBoundary
import PA194Site32ZeroBoundaryTo12
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroTo12Exact
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

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  F addCode ![PA194Site32ZeroToBoundaryExact.clock k args,modelNumeral M 7]

theorem zeroTo12 (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let a0 := (1 : M)+(1 : M)+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let w := F ones ![k+1,F sourceFileCode args]
    let p := w+w+1
    let r := (p+p)+(p+p)
    let r1 := r+r
    let r2 := r1+r1
    let r3 := r2+r2
    F PA194Stepper.stepper ![clock k args,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 12,F pairCode ![a3+1,r3]] := by
  dsimp only
  have h := PA194Site32ZeroToBoundaryExact.zeroToBoundary k args hz
  have h12 := PA194Site32ZeroBoundaryTo12.sevenTo12 (F ones ![k+1,F sourceFileCode args])
  dsimp only at h12
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h,h12]
#print axioms zeroTo12
end models
end PA194Site32ZeroTo12Exact
