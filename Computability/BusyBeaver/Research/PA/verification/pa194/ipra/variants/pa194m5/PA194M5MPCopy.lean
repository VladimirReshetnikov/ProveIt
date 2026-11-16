import PA194ProgramCopy
import PA194M5Program
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194M5MPCopy
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ProgramDrain PA194M5Program
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem entryRows : PA194ProgramCopy.Rows program 3647 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | rw [programLength]; decide | decide +kernel

theorem successRows : PA194ProgramCopy.Rows program 3714 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
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

theorem entry (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) :
    ReachesPositive program (sourceState 3647 a tail)
      (sourceState 3654 (Function.update a 1 (a 1+a 4)) tail) := by
  exact PA194ProgramCopy.copy program 3647 entryRows a tail hx

theorem success (a : Fin 11 → M) (tail : M) (hx : a 6 = 0) :
    ReachesPositive program (sourceState 3714 a tail)
      (sourceState 3721 (Function.update a 1 (a 1+a 4)) tail) := by
  exact PA194ProgramCopy.copy program 3714 successRows a tail hx
#print axioms entryRows
#print axioms successRows
#print axioms entry
#print axioms success
end models
end PA194M5MPCopy
