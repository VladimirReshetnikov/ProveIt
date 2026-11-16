import PA194ProgramGuard
import PA194M5Program
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5MPGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ProgramDrain PA194M5Program
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem rows : PA194ProgramGuard.Rows program 3682 := by
  refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
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

theorem guard (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) :
    ReachesPositive program (sourceState 3682 a tail)
      (sourceState (if a 1 = a 5 then 3695 else 3721) (PA194ProgramGuard.clear a) tail) := by
  exact PA194ProgramGuard.guard program 3682 rows a tail hx
#print axioms rows
#print axioms guard
end models
end PA194M5MPGuard
