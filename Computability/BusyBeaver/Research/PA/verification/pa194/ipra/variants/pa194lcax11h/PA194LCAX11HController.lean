import PA194TrieSourceController
import PA194LCAX11HChecks
import PA194LCAX11HBoxAgreement
import PA194LCAX11HInitializer

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194LCAX11HController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open ConPA.Machine ConPA.Machine.Compressed
open M6.Source (Instruction)
open PA194SourceControllerCode PA194SourceInstructionCalibration PA194SourceInstructionModel
open PA194SourcePCBound (pcModel)
open PA194IteratedSimulation PA194StateOne
open PA194CompressedSourceArgs PA194CompressedStartup PA194FiniteControls
open PA194LCAX11HChecks

private theorem pathShort (i : Nat) : (PA194LCAX11HData.path i).length ≤ 48 :=
  PA194TrieRoot.path_short PA194LCAX11HData.sourceTrie (by decide +kernel) i

private theorem haltCheck :
    PA194SourceContracts.haltContract PA194LCAX11HData.machine PA194LCAX11HData.path 10 512 = true := by
  decide +kernel

def data : PA194TrieSourceController.Data where
  table := PA194LCAX11HData.table
  machine := PA194LCAX11HData.machine
  label := PA194LCAX11HData.denseControl
  path := PA194LCAX11HData.path
  codeAt := PA194LCAX11HData.codeAt
  rows := PA194LCAX11HRows.rowAgreement
  rootControl := PA194LCAX11HRows.rootControl
  haltControl := PA194LCAX11HRows.haltControl
  pathShort := pathShort
  haltCheck := haltCheck

private theorem haltMask :
    PA194AX11HSource.program.map (fun instruction => decide (instruction = some .halt)) =
      (List.replicate 3671 false).set 10 true := by
  decide +kernel

private theorem haltIndex (i : Nat) (hi : i < 3671)
    (lookup : programAt i = some .halt) : i = 10 := by
  have hlen : i < PA194AX11HSource.program.length := by
    simpa only [PA194AX11HSource.program_length] using hi
  have row : PA194AX11HSource.program[i]? = some (some .halt) := by
    unfold programAt at lookup
    rw [List.getElem?_eq_getElem hlen] at lookup ⊢
    exact congrArg some lookup
  by_contra h
  have hm := congrArg (fun mask : List Bool => mask[i]?) haltMask
  rw [List.getElem?_map, row, List.getElem?_set_ne (Ne.symm h),
    List.getElem?_replicate_of_lt hi] at hm
  exact Bool.noConfusion (Option.some.inj hm)

private theorem targetBound (target : Option Nat)
    (valid : target.any (fun i => decide (i < 3671)) = true) : destination target < 3671 := by
  cases target with
  | none => simp at valid
  | some i => simpa only [PA194FoldedSourceContracts.destination_eq, Option.getD_some, Option.any_some, decide_eq_true_eq] using valid

private theorem atSite (i : Nat) (checked : checkAt i = true) :
    ∃ instr, programAt i = some instr ∧ PA194TrieSourceController.BoundedContracts data 3671 i instr := by
  obtain ⟨instr, lookup, _, valid, cert⟩ := checked_at i checked
  refine ⟨instr, lookup, ?_⟩
  cases instr with
  | halt => exact cert
  | jump next =>
    exact ⟨targetBound next valid, by simpa only [PA194FoldedSourceContracts.destination_eq, PA194TrieSourceController.contract, data] using (Bool.and_eq_true_iff.mp cert).2⟩
  | inc r next =>
    exact ⟨targetBound next valid, by simpa only [PA194FoldedSourceContracts.destination_eq, PA194TrieSourceController.contract, data] using (Bool.and_eq_true_iff.mp cert).2⟩
  | dec r zero positive =>
    obtain ⟨hz, hp⟩ := Bool.and_eq_true_iff.mp valid
    obtain ⟨cz, cp⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp cert).2
    exact ⟨targetBound zero hz, targetBound positive hp,
      by simpa only [PA194FoldedSourceContracts.destination_eq, PA194TrieSourceController.contract, data] using cz,
      by simpa only [PA194FoldedSourceContracts.destination_eq, PA194TrieSourceController.contract, data] using cp⟩

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
  exact PA194LCAX11HBoxAgreement.concreteBoxAgreement (tapeArgs s count spare) count br
    (readTail s count spare) hbranch

theorem halt_absorbs (y : M) (h : π₁ y = (194 : M)) : step PA194LCAX11HData.table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : M) at h
    rw [← h, pair_unpair, pair_unpair]
  conv_lhs => rw [he]
  rw [PA194LCAX11HData.table, PA194BModelSteps.halted PA194LCAX11HData.rows PA194LCAX11HRows.rowCount, ← he]

theorem advance (checks : AllContracts) (s gap count spare : M)
    (bound : F pc ![s] < modelNumeral M 3671) (normal : F pc ![s] ≠ modelNumeral M 10) :
    ∃ nextGap nextCount : M, F pc ![F PA194AX11HSource.step ![s]] < modelNumeral M 3671 ∧
      Reach1 data.table (F (PA194TrieSourceController.sourceRootCode data) ![s,gap,count,spare])
        (F (PA194TrieSourceController.sourceRootCode data) ![F PA194AX11HSource.step ![s],nextGap,nextCount,spare]) := by
  obtain ⟨i, hi⟩ := modelBelowNumeral 3671 (F pc ![s]) bound
  obtain ⟨instr, lookup, cert⟩ := atSite i.val (checks i.val i.isLt)
  have nonterminal : instr ≠ .halt := by
    intro h
    subst instr
    exact normal (by rwa [haltIndex i.val i.isLt lookup] at hi)
  have hlen : i.val < PA194AX11HSource.program.length := by
    simpa only [PA194AX11HSource.program_length] using i.isLt
  have row : PA194AX11HSource.program[i.val]'hlen = some instr := by
    simpa only [programAt, List.getElem?_eq_getElem hlen, Option.join_some] using lookup
  let s' := F PA194AX11HSource.step ![s]
  have hstep := PA194AX11HSource.selected i.val i.isLt s hi
  rw [row] at hstep
  have ⟨hpc, hregs⟩ := instructionCalibration (some instr) s (regs s) (fun _ => rfl)
  rw [← hstep] at hpc hregs
  exact PA194TrieSourceController.advanceAt data 3671 (by decide)
    s s' gap count spare ⟨i.val, by have := i.isLt; omega⟩ instr hi (literalBoxes spare)
    cert nonterminal ((pcModel s').trans hpc) (funext hregs)

theorem halt_iff_site10 (checks : AllContracts) :
    (∃ t : M, π₁ (ConPA.Machine.run PA194LCAX11HData.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F (iterate PA194AX11HSource.step) ![n,initialSource]] = modelNumeral M 10 := by
  apply PA194VariantController.halt_iff_site data.table 194
    (PA194TrieSourceController.sourceRootCode data) PA194AX11HSource.step
    (modelNumeral M 10) (modelNumeral M 3671) initialSource (57922 : M)
    initialSpare 0 (modelNumeral M 25)
  · rw [initialPC]
    exact modelNumeralStrict 25 3671 (by decide)
  · exact PA194LCAX11HInitializer.startup_root
  · intro s gap count bound
    have h := lt_trans bound (modelNumeralStrict 3671 3673 (by decide))
    obtain ⟨i, hi⟩ := modelBelowNumeral 3673 (F pc ![s]) h
    have root := PA194TrieRoot.sourceRoot_eval data.path data.label data.rootControl s gap count initialSpare i hi
    change F (PA194TrieSourceController.sourceRootCode data) ![s,gap,count,initialSpare] = _ at root
    rw [root, PA194SourceContracts.root, PA194SourceContracts.encodeControl]
    change (data.label 84 : M) ≠ (194 : M)
    rw [data.rootControl]
    norm_num
  · exact halt_absorbs
  · intro s gap count bound normal
    obtain ⟨gap', count', bound', k, hk, hrun⟩ := advance checks s gap count initialSpare bound normal
    exact ⟨k, gap', count', hk, bound', hrun⟩
  · exact PA194TrieSourceController.terminal data initialSpare (literalBoxes initialSpare)

#print axioms advance
#print axioms halt_iff_site10
end models
end PA194LCAX11HController
