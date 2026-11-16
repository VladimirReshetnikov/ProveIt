import PA194ModelCantorWalker
import PA194AXReaderAlgebra

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace PA194ModelAXReader
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194ModelMPDrain PA194ModelCantorWalker PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

structure ReaderRows (base : Nat) (input target : Fin 9) : Prop where
  walker : Rows base input
  input_ne6 : input ≠ 6
  input_ne7 : input ≠ 7
  target_ne6 : target ≠ 6
  tailTest : row (base+8) = some (.dec 7 (some (base+11)) (some (base+9)))
  tailInc : row (base+9) = some (.inc input (some (base+10)))
  tailBack : row (base+10) = some (.jump (some (base+8)))
  valueTest : row (base+11) = some (.dec 6 (some (base+14)) (some (base+12)))
  valueInc : row (base+12) = some (.inc target (some (base+13)))
  valueBack : row (base+13) = some (.jump (some (base+11)))
  valid : base+13 < 3673

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

theorem reader (base : Nat) (input target : Fin 9) (rows : ReaderRows base input target)
    (args : Fin 11 → M) (tail : M) :
    let code := cantor (args 6) (args 7) + args (location input)
    let decoded := argsAt input args (F fixedFirst ![code]) (F fixedSecond ![code]) 0
    let afterTail := argsAfter decoded 7 [input] (decoded 7)
    let output := argsAfter afterTail 6 [target] (afterTail 6)
    ReachesPositive (sourceState base args tail) (sourceState (base+14) output tail) := by
  dsimp only
  let code := cantor (args 6) (args 7) + args (location input)
  let decoded := argsAt input args (F fixedFirst ![code]) (F fixedSecond ![code]) 0
  let afterTail := argsAfter decoded 7 [input] (decoded 7)
  have tailLoop : Increments (base+8) (base+9) [input] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.tailInc
      (.jump _ (by have := rows.valid; omega) rows.tailBack)
  have valueLoop : Increments (base+11) (base+12) [target] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.valueInc
      (.jump _ (by have := rows.valid; omega) rows.valueBack)
  have hw := walk base input rows.walker rows.input_ne6 rows.input_ne7 args tail
  change ReachesPositive (sourceState base args tail) (sourceState (base+8) decoded tail) at hw
  have ht := drain (base+8) (base+9) (base+11) 7 [input]
    (by have := rows.valid; omega) rows.tailTest tailLoop (by simpa using Ne.symm rows.input_ne7) decoded tail
  change ReachesPositive (sourceState (base+8) decoded tail)
    (sourceState (base+11) afterTail tail) at ht
  have hv := drain (base+11) (base+12) (base+14) 6 [target]
    (by have := rows.valid; omega) rows.valueTest valueLoop (by simpa using Ne.symm rows.target_ne6) afterTail tail
  exact appendPositive (append hw.reaches ht.reaches) hv


#print axioms reader
end models
end PA194ModelAXReader
