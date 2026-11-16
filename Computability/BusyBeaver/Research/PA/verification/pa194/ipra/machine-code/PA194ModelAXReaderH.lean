import PA194ModelAXReader
import PA194AXReaderRows131
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace PA194ModelAXReaderH
open M6.Source PA194ModelAXReader PA194AXReaderRows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194ModelMPDrain PA194ModelCantorWalker PA194MachineProjections
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

theorem rows : ReaderRows 131 8 5 where
  walker := {
    valid := by decide
    input := s131
    advanceY := s132
    testX := s133
    pass := s134
    drainY := s135
    advanceX := s136
    repeatY := s137
    repeatInput := s138
  }
  input_ne6 := by decide
  input_ne7 := by decide
  target_ne6 := by decide
  tailTest := s139
  tailInc := s140
  tailBack := s141
  valueTest := s142
  valueInc := s143
  valueBack := s144
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
    ReachesPositive (sourceState 131 args tail)
      (sourceState 145
        (Function.update (Function.update (Function.update (Function.update args 8 (F fixedSecond ![args 8]))
          5 (args 5 + F fixedFirst ![args 8])) 6 0) 7 0) tail) := by
  have h := reader 131 8 5 rows args tail
  dsimp only at h
  have hzero : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hx,hy,hzero,zero_add] at h
  change ReachesPositive (sourceState 131 args tail)
    (sourceState 145
      (argsAfter (argsAfter (PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8]))
        7 [8] ((PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8])) 7))
        6 [5] ((argsAfter (PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8]))
        7 [8] ((PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8])) 7)) 6)) tail) at h
  rw [PA194AXReaderAlgebra.outputH] at h
  exact h

#print axioms execute
end models
end PA194ModelAXReaderH
