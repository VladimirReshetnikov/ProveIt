import PA194AX11HWindowWalkerLoop
import PA194ModelAXReader
import PA194AXReaderAlgebra

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace PA194WindowReader
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194ModelMPDrain PA194ModelCantorWalker PA194MachineProjections PA194ModelAXReader PA194WindowDrain PA194WindowWalkerLoop
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

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

theorem reader (code : Code 1) (lower bound base : Nat)
    (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+13 < bound) (input target : Fin 9) (rows : ReaderRows base input target)
    (args : Fin 11 → M) (tail : M) :
    let number := cantor (args 6) (args 7) + args (location input)
    let decoded := argsAt input args (F fixedFirst ![number]) (F fixedSecond ![number]) 0
    let afterTail := argsAfter decoded 7 [input] (decoded 7)
    let output := argsAfter afterTail 6 [target] (afterTail 6)
    PA194PausedReach.Reaches code (sourceState base args tail) (sourceState (base+14) output tail) := by
  dsimp only
  let number := cantor (args 6) (args 7) + args (location input)
  let decoded := argsAt input args (F fixedFirst ![number]) (F fixedSecond ![number]) 0
  let afterTail := argsAfter decoded 7 [input] (decoded 7)
  have tailLoop : SafeIncrements lower bound (base+8) (base+9) [input] :=
    .inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.tailInc
      (.jump _ (by have := rows.valid; omega) (by omega) (by omega) rows.tailBack)
  have valueLoop : SafeIncrements lower bound (base+11) (base+12) [target] :=
    .inc _ _ _ _ (by have := rows.valid; omega) (by omega) (by omega) rows.valueInc
      (.jump _ (by have := rows.valid; omega) (by omega) (by omega) rows.valueBack)
  have hw := PA194WindowWalkerLoop.walk code lower bound base hagrees hbase (by omega) input rows.walker rows.input_ne6 rows.input_ne7 args tail
  change PA194PausedReach.Reaches code (sourceState base args tail) (sourceState (base+8) decoded tail) at hw
  have ht := PA194WindowDrain.drain code lower bound hagrees (base+8) (base+9) (base+11) 7 [input]
    (by have := rows.valid; omega) (by omega) (by omega) rows.tailTest tailLoop (by simpa using Ne.symm rows.input_ne7) decoded tail
  change PA194PausedReach.Reaches code (sourceState (base+8) decoded tail)
    (sourceState (base+11) afterTail tail) at ht
  have hv := PA194WindowDrain.drain code lower bound hagrees (base+11) (base+12) (base+14) 6 [target]
    (by have := rows.valid; omega) (by omega) (by omega) rows.valueTest valueLoop (by simpa using Ne.symm rows.target_ne6) afterTail tail
  exact PA194PausedReach.append code (PA194PausedReach.append code hw ht) hv


#print axioms reader
end models
end PA194WindowReader
