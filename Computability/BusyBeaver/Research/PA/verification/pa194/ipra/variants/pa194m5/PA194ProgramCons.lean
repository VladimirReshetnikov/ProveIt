import PA194ProgramCantorWalker
import PA194ProgramTransfer
import PA194ProgramCantorPair

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace PA194ProgramCons
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ProgramDrain PA194SchedulerFetchPositive
open PA194ModelMPDrain (location)
open PA194ModelCantorWalker (argsAt write)
open PA194ModelMPTransfer (transferArgs)
open PA194ModelMPPair (values)
open PA194DiagonalLink PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

structure Rows (program : Program) (base coefficient : Nat) : Prop where
  pop : PA194ProgramCantorWalker.Rows program base 2
  restore : PA194ProgramTransfer.TransferRows program (base+8) (base+11) 7 2
  pair : PA194ProgramCantorPair.Rows program (base+11)
  multiplyValid : base+21 < program.length
  multiplyTest : row program (base+21) =
    some (.dec 7 (some (base+23+coefficient)) (some (base+22)))
  multiplyLoop : Increments program (base+21) (base+22)
    (List.replicate coefficient (1 : Fin 9))

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

noncomputable def implicationValue (coefficient : Nat) (left right : M) : M :=
  modelNumeral M coefficient * cantor left right

noncomputable def output (coefficient : Nat) (args : Fin 11 → M) (left rest : M) : Fin 11 → M :=
  Function.update (Function.update (Function.update (Function.update args
    1 (implicationValue coefficient left (args 1))) 2 rest) 6 0) 7 0

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Pop one Cantor stack entry and form the coefficient-dependent implication.
    The two scratch registers start and finish zero. -/
theorem execute (program : Program) (base coefficient : Nat) (rows : Rows program base coefficient)
    (args : Fin 11 → M) (tail left rest : M) (hx : args 6 = 0) (hy : args 7 = 0)
    (hstack : args 2 = cantor left rest) :
    ReachesPositive program (sourceState base args tail)
      (sourceState (base+23+coefficient) (output coefficient args left rest) tail) := by
  let popped := argsAt 2 args left rest 0
  let restored := transferArgs popped 7 2
  let paired := values restored 0 0 (cantor (restored 6) (restored 1))
  have hp := PA194ProgramCantorWalker.walk program base 2 rows.pop (by decide) (by decide) args tail
  change ReachesPositive program (sourceState base args tail) (sourceState (base+8)
    (argsAt 2 args (F fixedFirst ![cantor (args 6) (args 7)+args 2])
      (F fixedSecond ![cantor (args 6) (args 7)+args 2]) 0) tail) at hp
  have hzero : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hx,hy,hzero,zero_add,hstack,fixedFirst_model,first_cantor,fixedSecond_model,second_cantor] at hp
  change ReachesPositive program (sourceState base args tail) (sourceState (base+8) popped tail) at hp
  have hr := PA194ProgramTransfer.transfer program (base+8) (base+11) 7 2 rows.restore (by decide) popped tail
  change ReachesPositive program (sourceState (base+8) popped tail)
    (sourceState (base+11) restored tail) at hr
  have hy' : restored 7 = (0 : M) := by simp [restored,transferArgs,location]
  have hpair := PA194ProgramCantorPair.pair program (base+11) rows.pair restored tail hy'
  change ReachesPositive program (sourceState (base+11) restored tail)
    (sourceState (base+21) paired tail) at hpair
  have hm := multiply program (base+21) (base+22) (base+23+coefficient) coefficient
    rows.multiplyValid rows.multiplyTest rows.multiplyLoop paired tail
  have houtput : Function.update (Function.update paired
      1 (paired 1+modelNumeral M coefficient * paired 7)) 7 0 =
      output coefficient args left rest := by
    funext i
    fin_cases i <;> simp [paired,restored,popped,values,transferArgs,location,argsAt,write,output,implicationValue]
  rw [houtput] at hm
  exact appendPositive program (append program (append program hp.reaches hr.reaches) hpair.reaches) hm

#print axioms execute
end models
end PA194ProgramCons
