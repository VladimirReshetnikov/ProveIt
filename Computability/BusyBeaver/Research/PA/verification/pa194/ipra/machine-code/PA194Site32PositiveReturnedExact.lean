import PA194Site32PositiveReturnExact
import PA194Site32PositiveClock
import PA194Site32ZeroRollback
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32PositiveReturnedExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194ReturnFile PA194ReturnFileMeaning
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

theorem positiveReturned (k m : M) (args : Fin 11 → M) (hm : args 6 = m+1) :
    F PA194Stepper.stepper ![F addCode ![PA194Site32PositiveClock.to4Clock k args,PA194Site32PositiveReturnExact.returnCost args],PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 6,F pairCode ![before k+before k+1,F sourceFileCode (Function.update args 6 m)]] := by
  let v := physicalArgs args
  let ev : Fin 9 → M := fun i => v i.succ.succ
  let ev6 : Fin 3 → M := fun i => ev i.succ.succ.succ.succ.succ.succ
  let e8 : Fin 3 → M := fun i => v ⟨i.val+8,by omega⟩
  have ht : (fun i : Fin 2 => ev6 i.succ) = (fun i : Fin 2 => e8 i.succ) := by
    funext i; fin_cases i <;> rfl
  have hv : ev6 0 = m+1 := hm
  let qorig := F ones ![ev6 0,F (fileCode 1) (fun i => ev6 i.succ)]
  let q := F ones ![m+1,F (fileCode 1) (fun i => e8 i.succ)]
  have hq : qorig = q := by dsimp only [qorig,q]; rw [hv,ht]
  let vecOrig : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,(qorig+qorig)+(qorig+qorig)]
  let carriedOrig := F (PA194CarryFile.leftCode 8) (Fin.cases (before k) vecOrig)
  let zOrig := carriedOrig+carriedOrig+1
  let vec : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
  let carried := F (PA194CarryFile.leftCode 8) (Fin.cases (before k) vec)
  let z := carried+carried+1
  have start := PA194Site32To4.to4 k args
  dsimp only at start
  change F PA194Stepper.stepper ![PA194Site32PositiveClock.to4Clock k args,PA194Site32Branch.entry k args] =
    F pairCode ![modelNumeral M 4,F pairCode ![zOrig+zOrig,qorig]] at start
  dsimp only [zOrig,carriedOrig,vecOrig] at start
  rw [hq] at start
  have hreturn := PA194Site32PositiveReturnExact.returnFile args (before k) m
  change F PA194Stepper.stepper ![PA194Site32PositiveReturnExact.returnCost args,F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
    F pairCode ![modelNumeral M 6,F pairCode ![before k+before k+1,F sourceFileCode (Function.update args 6 m)]] at hreturn
  rw [PA194StepperCompose.modelStepperCompose,start,hreturn]
#print axioms positiveReturned
end models
end PA194Site32PositiveReturnedExact
