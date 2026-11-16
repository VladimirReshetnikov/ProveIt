import PA194CompressedStartup
import PA194CompressedIncrementOracle
import PA194FiniteControls
import PA194TrieRoot
import PA194VariantController
import PA194CompressedSourceArgs
import PA194FoldedSourceContracts
import PA194SourceBoundedStep
import PA194SourceHaltUnique
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194TrieSourceController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open M6.Runtime
open M6.Source (Instruction resolveAt physicalRegister physicalRegister_lt)
open ConPA.Machine ConPA.Machine.Compressed
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceBoundedStep
open PA194SourcePCBound (pcModel)
open PA194SourceHaltUnique PA194SourceRegisterRelation PA194SourceInstructionCalibration
open PA194CompressedSourceFrame (args)
open PA194CompressedSourceArgs PA194CompressedBoxFiles PA194CompressedBoxOracle
open PA194CompressedIncrementOracle PA194CompressedStartup PA194FiniteControls PA194StateOne

/-- Exact table/trie interface for a primary-register-allocation machine.
    The row and halt certificates refer to the literal machine, while each
    checked site separately verifies that its resolved instruction agrees with
    the primary source program. -/
structure Data where
  table : ConPA.Machine.Table
  machine : M6.Zip.TMN
  label : Nat → Nat
  path : Nat → M6.Source.Path
  codeAt : Nat → Option Instruction
  rows : RowAgreement table machine label
  rootControl : label 84 = 24
  haltControl : label 254 = 194
  pathShort : ∀ i, (path i).length ≤ 48
  haltCheck : PA194SourceContracts.haltContract machine path 10 512 = true

variable (d : Data)

abbrev sourceRootCode : Code 4 := PA194TrieRoot.sourceRootCode d.path
abbrev contract := PA194SourceContracts.contract d.machine d.path
abbrev haltContract := PA194SourceContracts.haltContract d.machine d.path
abbrev checkInstruction := PA194SourceContracts.checkInstruction d.machine d.path
abbrev checkAt := PA194SourceContracts.checkAt d.machine d.path d.codeAt

def AllContracts : Prop := ∀ i : Nat, i < 3673 → checkAt d i = true

def Contracts (i : Nat) : Instruction → Prop
  | .inc r next => destination next < 3673 ∧
    contract d none i (destination next) 0 512 (.inc (physicalRegister r)) = true
  | .dec r z p => destination z < 3673 ∧ destination p < 3673 ∧
    contract d (some (physicalRegister r,true)) i (destination z) 0 512 .none = true ∧
    contract d (some (physicalRegister r,false)) i (destination p) 1 512 (.dec (physicalRegister r)) = true
  | .jump next => destination next < 3673 ∧ contract d none i (destination next) 0 512 .none = true
  | .halt => haltContract d i 512 = true

private theorem atSite (i : Nat) (h : checkAt d i = true) :
    ∃ code, resolveAt PA194SourceProgram.sites i = some code ∧ Contracts d i code := by
  obtain ⟨code, hresolve, hcheck⟩ := PA194SourceContracts.checked_at d.machine d.path d.codeAt i h
  refine ⟨code, hresolve, ?_⟩
  cases code <;> simpa only [checkInstruction, PA194SourceContracts.checkInstruction, Contracts,
    PA194FoldedSourceContracts.destination_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hcheck

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

noncomputable abbrev root (gap : M) (box : BoxSt → M) (i : Nat)
    (extra : Nat := 0) (eff : Eff := .none) : M :=
  PA194SourceContracts.root d.label d.path gap box i extra eff

def Boxes (spare : M) : Prop :=
  ∀ (s count : M) (br : Branch), BranchOK (tapeArgs s count spare) br →
    BoxAgreement d.table d.label br
      (boxValue (tapeArgs s count spare) (incremented (tapeArgs s count spare) count))

private theorem root_initial_file (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    root d gap box i 0 effect = root d gap (fun _ => box (.plain effect)) i :=
  PA194TrieRoot.root_initial_file d.path d.label d.rootControl gap box i effect

private theorem root_advanced_gap (gap : M) (box : BoxSt → M) (i : Nat) (effect : Eff) :
    root d gap box i 1 effect = root d (gap+1) box i 0 effect :=
  PA194TrieRoot.root_advanced_gap d.path d.label d.rootControl d.pathShort gap box i effect

private theorem sourceRoot_eval (s gap count spare : M) (i : Fin 3673)
    (hpc : F pc ![s] = modelNumeral M i.val) :
    F (sourceRootCode d) ![s,gap,count,spare] =
      root d gap (fun _ => F PA194RegisterPermutation.sourceFileCode (args s count spare)) i.val :=
  PA194TrieRoot.sourceRoot_eval d.path d.label d.rootControl s gap count spare i hpc

private theorem root_control (gap : M) (box : BoxSt → M) (i extra : Nat) (effect : Eff) :
    π₁ (root d gap box i extra effect) = (24 : M) := by
  rw [root, PA194SourceContracts.root, PA194SourceContracts.encodeControl]
  change (d.label 84 : M) = (24 : M)
  rw [d.rootControl]
  rfl

private theorem contract_sound (gap : M) {br : Branch} {box : BoxSt → M}
    (boxes : BoxAgreement d.table d.label br box) (i j extra fuel : Nat) (effect : Eff)
    (cert : contract d br i j extra fuel effect = true) :
    Reach1 d.table (root d gap box i) (root d gap box j extra effect) :=
  PA194SourceContracts.contract_sound d.rows d.path gap boxes i j extra fuel effect cert
private theorem stepAt (s s' gap count spare nextCount : M) (i j : Fin 3673)
    (hi : F pc ![s] = modelNumeral M i.val) (hj : F pc ![s'] = modelNumeral M j.val)
    (boxes : Boxes d spare) (br : Branch) (hb : BranchOK (tapeArgs s count spare) br)
    (extra : Bool) (eff : Eff)
    (cert : contract d br i.val j.val (if extra then 1 else 0) 512 eff = true)
    (hout : boxValue (tapeArgs s count spare) (incremented (tapeArgs s count spare) count)
      (.plain eff) = file (tapeArgs s' nextCount spare)) :
    Reach1 d.table (F (sourceRootCode d) ![s,gap,count,spare])
      (F (sourceRootCode d) ![s',(if extra then gap+1 else gap),nextCount,spare]) := by
  let a := tapeArgs s count spare
  let box := boxValue a (incremented a count)
  have hin : box (.plain .none) = F PA194RegisterPermutation.sourceFileCode (args s count spare) :=
    (frameFile s count spare).symm
  rw [←frameFile] at hout
  change box (.plain eff) = F PA194RegisterPermutation.sourceFileCode (args s' nextCount spare) at hout
  have hstart : root d gap box i.val =
      root d gap (fun _ => F PA194RegisterPermutation.sourceFileCode (args s count spare)) i.val := by
    rw [root_initial_file d gap box i.val .none, hin]
  have hfinish (g : M) : root d g box j.val 0 eff =
      root d g (fun _ => F PA194RegisterPermutation.sourceFileCode (args s' nextCount spare)) j.val := by
    rw [root_initial_file d g box j.val eff, hout]
  have h := contract_sound d gap (boxes s count br hb) i.val j.val (if extra then 1 else 0) 512 eff cert
  change Reach1 d.table (root d gap box i.val) (root d gap box j.val (if extra then 1 else 0) eff) at h
  rw [sourceRoot_eval d s gap count spare i hi, sourceRoot_eval d _ _ _ _ j hj]
  cases extra with
  | false =>
    change Reach1 d.table (root d gap box i.val) (root d gap box j.val 0 eff) at h
    rw [hstart, hfinish] at h
    exact h
  | true =>
    change Reach1 d.table (root d gap box i.val) (root d gap box j.val 1 eff) at h
    rw [root_advanced_gap d gap box j.val eff, hstart, hfinish] at h
    exact h

/-- Execute each nonterminal instruction and reach the next source root. -/
theorem advance (checks : AllContracts d) (spare : M) (boxes : Boxes d spare) :
    ∀ s : M, F pc ![s] < modelNumeral M 3673 → F pc ![s] ≠ modelNumeral M 10 →
    ∀ gap count : M, ∃ nextGap nextCount : M,
      F pc ![F step ![s]] < modelNumeral M 3673 ∧
      Reach1 d.table (F (sourceRootCode d) ![s,gap,count,spare])
        (F (sourceRootCode d) ![F step ![s],nextGap,nextCount,spare]) := by
  classical
  intro s hbound hnormal gap count
  let s' : M := F step ![s]
  let a := tapeArgs s count spare
  let inc := incremented a count
  obtain ⟨i,hi,hpc,hregs⟩ := boundedStepCalibration s (regs s) hbound (by intro r; rfl)
  obtain ⟨instr,hinst,hc⟩ := atSite d i.val (checks i.val i.isLt)
  have ht : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie i.val).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some instr := by
    rwa [←PA194SourceProgram.resolve_tree]
  rw [ht] at hpc hregs
  have hl : regs s' = (execute (some instr) (regs s)).2 := funext hregs
  have hpc' : F pc ![s'] = modelNumeral M (execute (some instr) (regs s)).1 :=
    (pcModel s').trans hpc
  have bslot (r : Fin 9) : physicalRegister r < 9 := physicalRegister_lt r
  have read (r : Fin 9) : a (slot (position r)) = regs s r := readRegister s count spare r
  cases instr with
  | halt =>
    exfalso
    exact hnormal (by rwa [resolvedHaltIndex i.val hinst] at hi)
  | jump next =>
    obtain ⟨hb,hc⟩ := hc
    let j : Fin 3673 := ⟨destination next,hb⟩
    refine ⟨gap,count,?_,?_⟩
    · rw [hpc']
      exact modelNumeralStrict _ _ hb
    · have hout : boxValue a inc (.plain .none) = file (tapeArgs s' count spare) := by
        rw [sameRegisters s s' count spare hl]
        rfl
      exact stepAt d s s' gap count spare count i j hi hpc' boxes none trivial false .none hc hout
  | inc r next =>
    obtain ⟨hb,hc⟩ := hc
    let j : Fin 3673 := ⟨destination next,hb⟩
    refine ⟨gap,count+1,?_,?_⟩
    · rw [hpc']
      exact modelNumeralStrict _ _ hb
    · have hout : boxValue a inc (.plain (.inc (physicalRegister r))) =
          file (tapeArgs s' (count+1) spare) := by
        rw [incrementRegisters s s' count spare r hl]
        simp only [boxValue,bslot r,dite_true,inc,position]
        rfl
      exact stepAt d s s' gap count spare (count+1) i j hi hpc' boxes none trivial false _ hc hout
  | dec r zero positive =>
    obtain ⟨hzbound,hpbound,hzcheck,hpcheck⟩ := hc
    by_cases hz : regs s r = (0 : M)
    · simp only [execute,hz,if_true] at hpc' hl
      let j : Fin 3673 := ⟨destination zero,hzbound⟩
      have hb : BranchOK a (some (physicalRegister r,true)) := by
        intro hr
        change a (slot (position r)) = 0
        rw [read r,hz]
      refine ⟨gap,count,by rw [hpc']; exact modelNumeralStrict _ _ hzbound,?_⟩
      have hout : boxValue a inc (.plain .none) = file (tapeArgs s' count spare) := by
        rw [sameRegisters s s' count spare hl]
        rfl
      exact stepAt d s s' gap count spare count i j hi hpc' boxes _ hb false .none hzcheck hout
    · simp only [execute,hz,if_false] at hpc' hl
      let j : Fin 3673 := ⟨destination positive,hpbound⟩
      have hb : BranchOK a (some (physicalRegister r,false)) := by
        intro hr
        change a (slot (position r)) ≠ 0
        rw [read r]
        exact hz
      refine ⟨gap+1,count,by rw [hpc']; exact modelNumeralStrict _ _ hpbound,?_⟩
      have hout : boxValue a inc (.plain (.dec (physicalRegister r))) = file (tapeArgs s' count spare) := by
        rw [updatedRegisters s s' count spare _ r hl]
        simp only [boxValue,bslot r,dite_true,decrement,←read r,position]
        rfl
      exact stepAt d s s' gap count spare count i j hi hpc' boxes _ hb true _ hpcheck hout

theorem terminal (spare : M) (boxes : Boxes d spare) (s gap count : M)
    (hpc : F pc ![s] = modelNumeral M 10) :
    ∃ k : M, π₁ (ConPA.Machine.runFrom d.table k (F (sourceRootCode d) ![s,gap,count,spare])) = (194 : M) := by
  let a := tapeArgs s count spare
  let box := boxValue a (incremented a count)
  obtain ⟨last, ⟨k, _, hrun⟩, hend⟩ :=
    PA194SourceContracts.halt_sound d.rows d.path d.haltControl gap (boxes s count none trivial) 10 512 d.haltCheck
  change ConPA.Machine.runFrom d.table k (root d gap box 10) = last at hrun
  have hin : box (.plain .none) = F PA194RegisterPermutation.sourceFileCode (args s count spare) :=
    (frameFile s count spare).symm
  rw [root_initial_file d, hin, ←sourceRoot_eval d s gap count spare ⟨10,by decide⟩ hpc] at hrun
  exact ⟨k, by rw [hrun]; exact hend⟩

/-- Shared source controller for any checked primary-layout table and trie.
    Only startup, halt absorption, the concrete boxes and finite site checks
    are supplied by the candidate-specific specialization. -/
theorem halt_iff_controller (checks : AllContracts d) (boxes : Boxes d (initialSpare (M := M)))
    (startup : M)
    (initial : ConPA.Machine.run d.table startup =
      F (sourceRootCode d) ![initialSource,0,modelNumeral M 25,initialSpare])
    (absorb : ∀ c : M, π₁ c = (194 : M) → ConPA.Machine.step d.table c = c) :
    (∃ t : M, π₁ (ConPA.Machine.run d.table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n,initialSource]] = modelNumeral M 3674 := by
  refine PA194VariantController.halt_iff_controller d.table 194 (sourceRootCode d) initialSource startup
    initialSpare 0 (modelNumeral M 25) ?_ initial ?_ absorb ?_ (terminal d initialSpare boxes)
  · rw [initialPC]
    exact modelNumeralStrict 25 3673 (by decide)
  · intro s gap count hpc
    obtain ⟨i, hi⟩ := modelBelowNumeral 3673 (F pc ![s]) hpc
    rw [sourceRoot_eval d s gap count _ i hi, root_control]
    norm_num
  · intro s gap count hs hn
    obtain ⟨nextGap, nextCount, hpc, k, hk, hrun⟩ := advance d checks _ boxes s hs hn gap count
    exact ⟨k, nextGap, nextCount, hk, hpc, hrun⟩

#print axioms advance
#print axioms terminal
#print axioms halt_iff_controller
end models
end PA194TrieSourceController
