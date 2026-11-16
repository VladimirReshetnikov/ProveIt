import PA194ControllerSchedulerCore
set_option autoImplicit false
namespace PA194AX11HCacheFlag
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194SchedulerCode PA194StackCode PA194BranchSeed PA194TargetProofLeaf
 PA194TargetLeaves PA194TargetGate PA194SchedulerIteration
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PA194ControllerScheduler
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

theorem halt_iff (s : M) :
    F (haltAtK true) ![s] = 1 ↔ F (head fN fL) ![s] = 0 ∧ F fH ![s] = 1 := by
  have test : F (shiftHaltC fH) ![s] = 1 ↔ F fH ![s] = 1 := by
    rw [shiftHaltC, modelBin, modelNumeralCode]
    simp only [Nat.cast_one]
    change F equalityCode ![F fH ![s],1] = F oneCode Fin.elim0 ↔ _
    exact (modelEqualityCode (F fH ![s]) (1 : M)).2
  simp only [haltAtK, if_true, choose0_model]
  by_cases h : F (head fN fL) ![s] = (0 : M)
  · simpa only [h, if_true, true_and] using test
  · rw [if_neg h, PRAMultiplication.modelZero]
    simp only [h, false_and, iff_false]
    change (0 : M) ≠ 1
    exact _root_.zero_ne_one

#print axioms halt_iff
end models
end PA194AX11HCacheFlag
