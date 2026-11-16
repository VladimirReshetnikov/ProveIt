import PA194Site32ZeroFile
import PA194Site32Branch
import PA194Site32PositiveClock
import PA194Site32ZeroRollback
import PA194Site32To4
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroRollbackExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194ReturnFile PA194ReturnFileMeaning
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194Site32ZeroFile PA194Site32ZeroRollback
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
  F addCode ![PA194Site32PositiveClock.to4Clock k args,
    F addCode ![F addCode ![modelNumeral M 1,modelNumeral M 2],F (PA194CarryFile.costCode 9) (nine args)]]

theorem zeroRollback (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    F PA194Stepper.stepper ![clock k args,PA194Site32Branch.entry k args] =
      F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),
        F parityCode (fun _ => before k)+F sourceFileCode args+F sourceFileCode args]] := by
  let v := physicalArgs args
  let t := tailWord args
  let q := F ones ![(0 : M),t+t]
  let vec : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,(q+q)+(q+q)]
  let carried := F (PA194CarryFile.leftCode 8) (Fin.cases (before k) vec)
  let z := carried+carried+1
  let ev : Fin 9 → M := fun i => v i.succ.succ
  let ev6 : Fin 3 → M := fun i => ev i.succ.succ.succ.succ.succ.succ
  have htail : (fun i : Fin 2 => ev6 i.succ) = (fun i : Fin 2 => v ⟨i.val+9,by omega⟩) := by
    funext i; fin_cases i <;> rfl
  have hselected : ev6 0 = (0 : M) := hz
  have hq : F ones ![ev6 0,F (fileCode 1) (fun i => ev6 i.succ)] = q := by
    rw [hselected,htail,←tailIdentity]
  let qorig := F ones ![ev6 0,F (fileCode 1) (fun i => ev6 i.succ)]
  let vecOrig : Fin 9 → M := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,(qorig+qorig)+(qorig+qorig)]
  let carriedOrig := F (PA194CarryFile.leftCode 8) (Fin.cases (before k) vecOrig)
  let zOrig := carriedOrig+carriedOrig+1
  have start := PA194Site32To4.to4 k args
  dsimp only at start
  change F PA194Stepper.stepper ![PA194Site32PositiveClock.to4Clock k args,PA194Site32Branch.entry k args] =
    F pairCode ![modelNumeral M 4,F pairCode ![zOrig+zOrig,qorig]] at start
  have hqorig : qorig = q := hq
  dsimp only [zOrig,carriedOrig,vecOrig] at start
  rw [hqorig] at start
  let cost := F addCode ![F addCode ![modelNumeral M 1,modelNumeral M 2],F (PA194CarryFile.costCode 9) (nine args)]
  have hroll := PA194Site32ZeroRollbackCell.rollback (before k) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 9) (v 10)
  dsimp only at hroll
  change F PA194Stepper.stepper ![cost,F pairCode ![modelNumeral M 4,F pairCode ![z+z,q]]] =
    F pairCode ![modelNumeral M 11,F pairCode ![F halfCode (fun _ => before k),F parityCode (fun _ => before k)+returned args+returned args]] at hroll
  rw [returnedIsSourceFile args hz] at hroll
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,start,hroll]
#print axioms zeroRollback
end models
end PA194Site32ZeroRollbackExact
