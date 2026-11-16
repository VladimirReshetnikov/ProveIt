import PA194AX11HWindowReader
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
namespace PA194WindowReads
open M6.Source PA194ModelAXReader
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SchedulerFetchPositive
open PA194ModelMPDrain PA194ModelCantorWalker PA194MachineProjections PA194WindowDrain
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

theorem readH (code : Code 1) (lower bound base : Nat)
    (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+13 < bound) (rows : ReaderRows base 8 5) (args : Fin 11 → M) (tail : M)
    (hx : args 6 = (0 : M)) (hy : args 7 = (0 : M)) :
    PA194PausedReach.Reaches code (sourceState base args tail)
      (sourceState (base+14)
        (Function.update (Function.update (Function.update (Function.update args 8 (F fixedSecond ![args 8]))
          5 (args 5 + F fixedFirst ![args 8])) 6 0) 7 0) tail) := by
  have h := PA194WindowReader.reader code lower bound base hagrees hbase hbelow 8 5 rows args tail
  dsimp only at h
  have hzero : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hx,hy,hzero,zero_add] at h
  change PA194PausedReach.Reaches code (sourceState base args tail)
    (sourceState (base+14)
      (argsAfter (argsAfter (PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8]))
        7 [8] ((PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8])) 7))
        6 [5] ((argsAfter (PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8]))
        7 [8] ((PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8])) 7)) 6)) tail) at h
  rw [PA194AXReaderAlgebra.outputH] at h
  exact h

theorem readD (code : Code 1) (lower bound base : Nat)
    (hagrees : AgreesWindow (M := M) code lower bound) (hbase : lower ≤ base) (hbelow : base+13 < bound) (rows : ReaderRows base 8 4) (args : Fin 11 → M) (tail : M)
    (hx : args 6 = (0 : M)) (hy : args 7 = (0 : M)) :
    PA194PausedReach.Reaches code (sourceState base args tail)
      (sourceState (base+14)
        (Function.update (Function.update (Function.update (Function.update args 8 (F fixedSecond ![args 8]))
          4 (args 4 + F fixedFirst ![args 8])) 6 0) 7 0) tail) := by
  have h := PA194WindowReader.reader code lower bound base hagrees hbase hbelow 8 4 rows args tail
  dsimp only at h
  have hzero : cantor (0 : M) 0 = 0 := by simp [cantor,triangle]
  rw [hx,hy,hzero,zero_add] at h
  change PA194PausedReach.Reaches code (sourceState base args tail)
    (sourceState (base+14)
      (argsAfter (argsAfter (PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8]))
        7 [8] ((PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8])) 7))
        6 [4] ((argsAfter (PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8]))
        7 [8] ((PA194AXReaderAlgebra.decoded args (F fixedFirst ![args 8]) (F fixedSecond ![args 8])) 7)) 6)) tail) at h
  rw [PA194AXReaderAlgebra.outputD] at h
  exact h

#print axioms readD
#print axioms readH
end models
end PA194WindowReads
