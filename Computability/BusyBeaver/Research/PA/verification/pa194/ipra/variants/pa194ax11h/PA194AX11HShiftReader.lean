import PA194PausedReader
import PA194AX11HFetchAgree
import PA194ShiftReaderRows
import PA194ShiftReaderAlgebra
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace PA194AX11HShiftReader
open M6.Source PA194ModelAXReader PA194ShiftReaderRows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194ModelMPDrain PA194ModelCantorWalker PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem rows : ReaderRows 11 2 5 where
  walker := {
    valid := by decide
    input := s11
    advanceY := s12
    testX := s13
    pass := s14
    drainY := s15
    advanceX := s16
    repeatY := s17
    repeatInput := s18
  }
  input_ne6 := by decide
  input_ne7 := by decide
  target_ne6 := by decide
  tailTest := s19
  tailInc := s20
  tailBack := s21
  valueTest := s22
  valueInc := s23
  valueBack := s24
  valid := by decide

#print axioms rows

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

theorem execute (args : Fin 11 → M) (tail : M)
    (hx : args 6 = (0 : M)) (hy : args 7 = (0 : M)) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 11 args tail)
      (sourceState 25
        (Function.update (Function.update (Function.update (Function.update args 2 (F fixedSecond ![args 2]))
          5 (args 5 + F fixedFirst ![args 2])) 6 0) 7 0) tail) := by
  have h := PA194PausedReader.reader PA194AX11HSource.step 48 11
    PA194AX11HFetchAgree.agrees (by decide) 2 5 rows args tail
  dsimp only at h
  have hzero : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hx,hy,hzero,zero_add] at h
  change PA194PausedReach.Reaches PA194AX11HSource.step (sourceState 11 args tail)
    (sourceState 25
      (argsAfter (argsAfter (PA194ShiftReaderAlgebra.decoded args (F fixedFirst ![args 2]) (F fixedSecond ![args 2]))
        7 [2] ((PA194ShiftReaderAlgebra.decoded args (F fixedFirst ![args 2]) (F fixedSecond ![args 2])) 7))
        6 [5] ((argsAfter (PA194ShiftReaderAlgebra.decoded args (F fixedFirst ![args 2]) (F fixedSecond ![args 2]))
        7 [2] ((PA194ShiftReaderAlgebra.decoded args (F fixedFirst ![args 2]) (F fixedSecond ![args 2])) 7)) 6)) tail) at h
  rw [PA194ShiftReaderAlgebra.output] at h
  exact h

#print axioms execute
end models
end PA194AX11HShiftReader
