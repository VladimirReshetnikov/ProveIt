import PA194TrieSourceController
import PA194AX11HSource
import PA194AX11HInitializer

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194AX11HSharedController
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
open PA194TrieSourceController (Data Boxes sourceRootCode)

def programAt (i : Nat) : Option Instruction :=
  (PA194AX11HSource.program[i]?).join

/-- Check that a literal table implements the exact revised AX11H instruction. -/
def checkAt (machine : M6.Zip.TMN) (path : Nat → M6.Source.Path)
    (codeAt : Nat → Option Instruction) (i : Nat) : Bool :=
  decide (programAt i = codeAt i) &&
    (programAt i).any (PA194SourceContracts.checkInstructionFor 3671 machine path i)

def AllContracts (d : Data) : Prop :=
  ∀ i : Nat, i < 3671 → checkAt d.machine d.path d.codeAt i = true

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

private theorem atSite (d : Data) (i : Nat)
    (checked : checkAt d.machine d.path d.codeAt i = true) :
    ∃ instr, programAt i = some instr ∧ PA194TrieSourceController.BoundedContracts d 3671 i instr := by
  cases h : programAt i with
  | none => simp [checkAt, h] at checked
  | some instr =>
    have hcheck := (Bool.and_eq_true_iff.mp checked).2
    rw [h] at hcheck
    exact ⟨instr, rfl, PA194TrieSourceController.checkedInstructionContracts d 3671 i instr hcheck⟩

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

variable (d : Data)

/-- With the common startup path, reaching the same packed seed suffices to
    establish the initial source relation. -/
theorem startup_root_of_same_seed (time : M) (samePath : d.path 25 = PA194AX11HData.path 25)
    (seed : ConPA.Machine.run d.table time =
      ⟪(24 : M), (1 : M), (152919395647067130113387679226998336721518593 : M)⟫) :
    ConPA.Machine.run d.table time =
      F (sourceRootCode d) ![initialSource,0,modelNumeral M 25,initialSpare] := by
  rw [seed, ← PA194AX11HModelStartup.modeledStartup, PA194AX11HInitializer.startup_root]
  let i : Fin 3673 := ⟨25, by decide⟩
  rw [PA194TrieRoot.sourceRoot_eval PA194AX11HData.path PA194AX11HData.denseControl
    PA194AX11HRows.rootControl _ _ _ _ i initialPC]
  change _ = F (PA194TrieRoot.sourceRootCode d.path)
    ![initialSource,0,modelNumeral M 25,initialSpare]
  rw [PA194TrieRoot.sourceRoot_eval d.path d.label d.rootControl _ _ _ _ i initialPC]
  rw [PA194TrieRoot.root_eval _ _ PA194AX11HRows.rootControl,
    PA194TrieRoot.root_eval _ _ d.rootControl]
  change _ = ⟪(24 : M),(1 : M),PA194Path27Header.modelWord (d.path 25) _⟫
  rw [samePath]

theorem advance (checks : AllContracts d) (s gap count spare : M) (boxes : Boxes d spare)
    (bound : F pc ![s] < modelNumeral M 3671) (normal : F pc ![s] ≠ modelNumeral M 10) :
    ∃ nextGap nextCount : M, F pc ![F PA194AX11HSource.step ![s]] < modelNumeral M 3671 ∧
      Reach1 d.table (F (sourceRootCode d) ![s,gap,count,spare])
        (F (sourceRootCode d) ![F PA194AX11HSource.step ![s],nextGap,nextCount,spare]) := by
  obtain ⟨i, hi⟩ := modelBelowNumeral 3671 (F pc ![s]) bound
  obtain ⟨instr, lookup, cert⟩ := atSite d i.val (checks i.val i.isLt)
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
  exact PA194TrieSourceController.advanceAt d 3671 (by decide)
    s s' gap count spare ⟨i.val, by have := i.isLt; omega⟩ instr hi boxes
    cert nonterminal ((pcModel s').trans hpc) (funext hregs)

theorem halt_iff_site10 (checks : AllContracts d) (boxes : Boxes d (initialSpare : M))
    (time : M) (startup : ConPA.Machine.run d.table time =
      F (sourceRootCode d) ![initialSource,0,modelNumeral M 25,initialSpare])
    (absorbs : ∀ y : M, π₁ y = (194 : M) → step d.table y = y) :
    (∃ t : M, π₁ (ConPA.Machine.run d.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F (iterate PA194AX11HSource.step) ![n,initialSource]] = modelNumeral M 10 := by
  apply PA194VariantController.halt_iff_site d.table 194
    (sourceRootCode d) PA194AX11HSource.step
    (modelNumeral M 10) (modelNumeral M 3671) initialSource time
    initialSpare 0 (modelNumeral M 25)
  · rw [initialPC]
    exact modelNumeralStrict 25 3671 (by decide)
  · exact startup
  · intro s gap count bound
    have h := lt_trans bound (modelNumeralStrict 3671 3673 (by decide))
    obtain ⟨i, hi⟩ := modelBelowNumeral 3673 (F pc ![s]) h
    rw [PA194TrieSourceController.sourceRootFor_control d s gap count initialSpare i hi]
    norm_num
  · exact absorbs
  · intro s gap count bound normal
    obtain ⟨gap', count', bound', k, hk, hrun⟩ := advance d checks s gap count initialSpare boxes bound normal
    exact ⟨k, gap', count', hk, bound', hrun⟩
  · exact PA194TrieSourceController.terminal d initialSpare boxes

#print axioms startup_root_of_same_seed
#print axioms advance
#print axioms halt_iff_site10
end models
end PA194AX11HSharedController
