import PA194TrieSourceController
import PA194M6Checks
import PA194M6BoxAgreement
import PA194M6Initializer
import PA194M6Control

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194M6Controller
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open ConPA.Machine ConPA.Machine.Compressed
open M6.Source (Instruction)
open PA194SourceControllerCode (pc instruction)
open PA194SourceInstructionCalibration PA194SourceInstructionModel
open PA194SourcePCBound (pcModel)
open PA194IteratedSimulation PA194StateOne
open PA194CompressedSourceArgs PA194CompressedStartup PA194FiniteControls
open PA194M6Checks
open PA194M6Program (program programLength)

private theorem pathShort (i : Nat) : (PA194M6Data.path i).length ≤ 48 :=
  PA194TrieRoot.path_short PA194M6Data.sourceTrie (by decide +kernel) i

private theorem haltCheck :
    PA194SourceContracts.haltContract PA194M6Data.machine PA194M6Data.path 10 512 = true := by
  decide +kernel

def data : PA194TrieSourceController.Data where
  table := PA194M6Data.table
  machine := PA194M6Data.machine
  label := PA194M6Data.denseControl
  path := PA194M6Data.path
  codeAt := PA194M6Data.codeAt
  rows := PA194M6Rows.rowAgreement
  rootControl := PA194M6Rows.rootControl
  haltControl := PA194M6Rows.haltControl
  pathShort := pathShort
  haltCheck := haltCheck

private theorem atSite (i : Nat) (checked : checkAt i = true) :
    ∃ instr, programAt i = some instr ∧ (instr = .halt ↔ i = 10) ∧
      PA194TrieSourceController.BoundedContracts data 3795 i instr := by
  obtain ⟨instr, lookup, _, halt, cert⟩ := checked_at i checked
  exact ⟨instr, lookup, halt, PA194TrieSourceController.checkedInstructionContracts data 3795 i instr cert⟩

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

theorem literalBoxes (spare : M) : PA194TrieSourceController.Boxes data spare := by
  intro s count br hbranch
  exact PA194M6BoxAgreement.concreteBoxAgreement (tapeArgs s count spare) count br
    (readTail s count spare) hbranch

theorem halt_absorbs (y : M) (h : π₁ y = (194 : M)) : step PA194M6Data.table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h, pair_unpair, pair_unpair]
  conv_lhs => rw [he]
  rw [PA194M6Data.table, PA194BModelSteps.halted PA194M6Data.rows PA194M6Rows.rowCount, ← he]

theorem advance (checks : AllContracts) (s gap count spare : M)
    (bound : F pc ![s] < modelNumeral M 3795) (normal : F pc ![s] ≠ modelNumeral M 10) :
    ∃ nextGap nextCount : M, F pc ![F (PA194ProgramControl.step program) ![s]] < modelNumeral M 3795 ∧
      Reach1 data.table (F (PA194TrieRoot.sourceRootCodeFor data.path 3795) ![s,gap,count,spare])
        (F (PA194TrieRoot.sourceRootCodeFor data.path 3795) ![F (PA194ProgramControl.step program) ![s],nextGap,nextCount,spare]) := by
  obtain ⟨i, hi⟩ := modelBelowNumeral 3795 (F pc ![s]) bound
  obtain ⟨instr, lookup, halt, cert⟩ := atSite i.val (checks i.val i.isLt)
  have nonterminal : instr ≠ .halt := by
    intro h
    exact normal (by rwa [halt.mp h] at hi)
  have hlen : i.val < program.length := by simpa only [programLength] using i.isLt
  let s' := F (PA194ProgramControl.step program) ![s]
  have hstep := PA194ProgramControl.actionAt program i.val hlen s hi
  rw [show PA194ProgramControl.row program i.val = some instr from lookup] at hstep
  have action_eq : PA194ProgramControl.action program (some instr) = instruction (some instr) := by
    cases instr <;> simp_all [PA194ProgramControl.action]
  rw [action_eq, instructionModel] at hstep
  have ⟨hpc, hregs⟩ := instructionCalibration (some instr) s (regs s) (fun _ => rfl)
  rw [← hstep] at hpc hregs
  exact PA194TrieSourceController.advanceAtBound data 3795 le_rfl
    s s' gap count spare i instr hi (literalBoxes spare)
    cert nonterminal ((pcModel s').trans hpc) (funext hregs)

theorem halt_iff_site10 (checks : AllContracts) :
    (∃ t : M, π₁ (ConPA.Machine.run PA194M6Data.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F (iterate (PA194ProgramControl.step program)) ![n,initialSource]] = modelNumeral M 10 := by
  apply PA194VariantController.halt_iff_site data.table 194
    (PA194TrieRoot.sourceRootCodeFor data.path 3795) (PA194ProgramControl.step program)
    (modelNumeral M 10) (modelNumeral M 3795) initialSource (58320 : M)
    initialSpare 0 (modelNumeral M 25)
  · rw [initialPC]
    exact modelNumeralStrict 25 3795 (by decide)
  · exact PA194M6Initializer.startup_root
  · intro s gap count bound
    obtain ⟨i, hi⟩ := modelBelowNumeral 3795 (F pc ![s]) bound
    rw [PA194TrieSourceController.sourceRootFor_control data s gap count initialSpare i hi]
    norm_num
  · exact halt_absorbs
  · intro s gap count bound normal
    obtain ⟨gap', count', bound', k, hk, hrun⟩ := advance checks s gap count initialSpare bound normal
    exact ⟨k, gap', count', hk, bound', hrun⟩
  · exact fun s gap count hpc =>
      PA194TrieSourceController.terminalAt data initialSpare (literalBoxes initialSpare) s gap count
        (⟨10, by decide⟩ : Fin 3795) haltCheck hpc

#print axioms advance
#print axioms halt_iff_site10
end models
end PA194M6Controller
