import PA194ProgramCons
import PA194M5Constructor

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194M5Cons
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ProgramDrain PA194SchedulerFetchPositive PA194ProgramCons PA194M5Program
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem rows : Rows program 102 5 where
  pop := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  restore := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  pair := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  multiplyValid := by decide +kernel
  multiplyTest := by decide +kernel
  multiplyLoop := PA194M5Constructor.loopRows

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem firstCons (args : Fin 11 → M) (tail left rest : M)
    (hx : args 6 = 0) (hy : args 7 = 0) (hstack : args 2 = cantor left rest) :
    ReachesPositive program (sourceState 102 args tail)
      (sourceState 130 (output 5 args left rest) tail) :=
  execute program 102 5 rows args tail left rest hx hy hstack

#print axioms rows
#print axioms firstCons
end models
end PA194M5Cons
