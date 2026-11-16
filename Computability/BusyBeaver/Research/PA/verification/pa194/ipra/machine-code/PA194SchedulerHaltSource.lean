import PA194SchedulerBranchesOpen
import PA194ShiftModelHalt

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194SchedulerHaltSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAHerbrandSelection TableDispatch
open PA194SchedulerIteration PA194SchedulerCode PA194MachineShiftMPCode
open PA194SchedulerFetchPositive PA194IteratedSimulation

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

theorem haltFlag_iff (s : M) :
    F haltAt ![s] = (1 : M) ↔
      F (head fN fL) ![s] = (0 : M) ∧ F fT ![s] + F fH ![s] = 1 := by
  rw [haltAt,halt,choose0_model]
  by_cases hz : F (head fN fL) ![s] = (0 : M)
  · rw [if_pos hz,shiftHalt_correct]
    simp only [hz,true_and]
  · rw [if_neg hz,PRAMultiplication.modelZero]
    constructor
    · intro h
      exact (Arithmetic.one_ne_zero h.symm).elim
    · rintro ⟨he,_⟩
      exact (hz he).elim

/-- From an aligned site-25 root, a scheduler halt flag produces a literal
source-controller halt after a model-valued fetch and an exact SHIFT path. -/
theorem haltFromRoot (s : M) (args : Fin 11 → M) (suffix : M)
    (hn : F fN ![s] = args 0) (hl : F fL ![s] = args 8)
    (ht : F fT ![s] = args 1) (hh : F fH ![s] = args 5)
    (h3 : args 3 = (0 : M)) (hx : args 6 = 0) (hy : args 7 = 0)
    (hflag : F haltAt ![s] = 1) :
    ∃ c : M, F PA194SourceControllerCode.pc
      ![F PA194SourceControllerCode.run ![c,sourceState 25 args suffix]] =
        modelNumeral M 3674 := by
  obtain ⟨htag,hsum⟩ := (haltFlag_iff s).mp hflag
  obtain ⟨clock,out,_,_,_,h6,_,hshift,_,_,hkeep⟩ :=
    PA194SchedulerBranchesOpen.fetchDecodeBranchesPreserving s args suffix hn hl hx hy h3
  have htop := hkeep 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcache := hkeep 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsum' : out 1 + out 5 = (1 : M) := by
    rw [htop,hcache,←ht,←hh]
    exact hsum
  obtain ⟨c,hc⟩ := PA194ShiftModelHalt.halt_of_sum_one out suffix hsum' h6
  refine ⟨(clock+1)+c,?_⟩
  change F PA194SourceControllerCode.pc
    ![F (iterate PA194SourceControllerCode.step) ![(clock+1)+c,sourceState 25 args suffix]] = _
  rw [PA194IterateAddOpen.iterateAdd]
  change F PA194SourceControllerCode.pc ![F PA194SourceControllerCode.run
    ![c,F PA194SourceControllerCode.run ![clock+1,sourceState 25 args suffix]]] = _
  rw [hshift htag]
  exact hc

#print axioms haltFlag_iff
#print axioms haltFromRoot
end models
end PA194SchedulerHaltSource
