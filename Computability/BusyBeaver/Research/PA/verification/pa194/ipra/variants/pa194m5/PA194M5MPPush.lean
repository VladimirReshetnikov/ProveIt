import PA194ProgramPush
import PA194M5Program
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5MPPush
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ProgramDrain PA194M5Program
open PA194ModelMPPush (pushed)
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem entryRows : PA194ProgramPush.Rows program 3628 := by
  refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
  all_goals first | rw [programLength]; decide | decide +kernel

theorem successRows : PA194ProgramPush.Rows program 3695 := by
  refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
  all_goals first | rw [programLength]; decide | decide +kernel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem entry (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive program (sourceState 3628 a tail) (sourceState 3647 (pushed a) tail) := by
  exact PA194ProgramPush.push program 3628 entryRows a tail hx hy

theorem success (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) (hy : a 7 = 0) :
    ReachesPositive program (sourceState 3695 a tail) (sourceState 3714 (pushed a) tail) := by
  exact PA194ProgramPush.push program 3695 successRows a tail hx hy
#print axioms entryRows
#print axioms successRows
#print axioms entry
#print axioms success
end models
end PA194M5MPPush
