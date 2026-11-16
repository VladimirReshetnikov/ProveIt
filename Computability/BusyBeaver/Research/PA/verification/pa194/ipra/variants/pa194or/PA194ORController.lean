import PA194ORInitializer
import PA194ORBoxAgreement
import PA194VariantController
import PA194CompressedSourceArgs
import PA194FoldedSourceContracts
import PA194SourceBoundedStep
import PA194SourceHaltUnique

/-! Source-controller simulation from the checked OR contracts and the
literal implementations of the register operations. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194ORController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open M6.Runtime
open M6.Source (Instruction resolveAt physicalRegister physicalRegister_lt)
open ConPA.Machine.Compressed
open PA194ORData PA194ORRoot PA194ORChecks PA194ORPhysical
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceBoundedStep
open PA194SourcePCBound (pcModel)
open PA194SourceHaltUnique PA194SourceRegisterRelation PA194SourceInstructionCalibration
open PA194CompressedSourceFrame (args)
open PA194CompressedSourceArgs PA194CompressedBoxFiles PA194CompressedBoxOracle
open PA194CompressedIncrementOracle PA194CompressedStartup PA194FiniteControls PA194StateOne

def AllContracts : Prop := ∀ i : Nat, i < 3673 → PA194ORChecks.checkAt i = true

def Contracts (i : Nat) : Instruction → Prop
  | .inc r next => destination next < 3673 ∧
    contract none i (destination next) 0 512 (.inc (physicalRegister r)) = true
  | .dec r z p => destination z < 3673 ∧ destination p < 3673 ∧
    contract (some (physicalRegister r,true)) i (destination z) 0 512 .none = true ∧
    contract (some (physicalRegister r,false)) i (destination p) 1 512 (.dec (physicalRegister r)) = true
  | .jump next => destination next < 3673 ∧ contract none i (destination next) 0 512 .none = true
  | .halt => haltContract i 512 = true

private theorem atSite (i : Nat) (h : checkAt i = true) :
    ∃ code, resolveAt PA194SourceProgram.sites i = some code ∧ Contracts i code := by
  obtain ⟨code, hresolve, hcheck⟩ := checked_at i h
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

/-- Realization of the three register operations used by the compressed checker. -/
def Boxes (spare : M) : Prop :=
  ∀ (s count : M) (br : Branch), BranchOK (tapeArgs s count spare) br →
    BoxAgreement table denseControl br
      (boxValue (tapeArgs s count spare) (incremented (tapeArgs s count spare) count))

theorem literalBoxes (spare : M) : Boxes spare := by
  intro s count br hbranch
  exact PA194ORBoxAgreement.concreteBoxAgreement (tapeArgs s count spare) count br
    (readTail s count spare) hbranch

private theorem stepAt (s s' gap count spare nextCount : M) (i j : Fin 3673)
    (hi : F pc ![s] = modelNumeral M i.val) (hj : F pc ![s'] = modelNumeral M j.val)
    (boxes : Boxes spare) (br : Branch) (hb : BranchOK (tapeArgs s count spare) br)
    (extra : Bool) (eff : Eff)
    (cert : contract br i.val j.val (if extra then 1 else 0) 512 eff = true)
    (hout : boxValue (tapeArgs s count spare) (incremented (tapeArgs s count spare) count)
      (.plain eff) = file (tapeArgs s' nextCount spare)) :
    Reach1 table (F sourceRootCode ![s,gap,count,spare])
      (F sourceRootCode ![s',(if extra then gap+1 else gap),nextCount,spare]) := by
  let a := tapeArgs s count spare
  let box := boxValue a (incremented a count)
  have hin : box (.plain .none) = F PA194RegisterPermutation.sourceFileCode (args s count spare) :=
    (frameFile s count spare).symm
  rw [←frameFile] at hout
  change box (.plain eff) = F PA194RegisterPermutation.sourceFileCode (args s' nextCount spare) at hout
  have hstart : root gap box i.val =
      root gap (fun _ => F PA194RegisterPermutation.sourceFileCode (args s count spare)) i.val := by
    rw [root_initial_file gap box i.val .none, hin]
  have hfinish (g : M) : root g box j.val 0 eff =
      root g (fun _ => F PA194RegisterPermutation.sourceFileCode (args s' nextCount spare)) j.val := by
    rw [root_initial_file g box j.val eff, hout]
  have h := contract_sound gap (boxes s count br hb) i.val j.val (if extra then 1 else 0) 512 eff cert
  change Reach1 table (root gap box i.val) (root gap box j.val (if extra then 1 else 0) eff) at h
  rw [sourceRoot_eval s gap count spare i hi, sourceRoot_eval _ _ _ _ j hj]
  cases extra with
  | false =>
    change Reach1 table (root gap box i.val) (root gap box j.val 0 eff) at h
    rw [hstart, hfinish] at h
    exact h
  | true =>
    change Reach1 table (root gap box i.val) (root gap box j.val 1 eff) at h
    rw [root_advanced_gap gap box j.val eff, hstart, hfinish] at h
    exact h

/-- Execute each nonterminal instruction and reach the next OR source root. -/
theorem advance (checks : AllContracts) (spare : M) (boxes : Boxes spare) :
    ∀ s : M, F pc ![s] < modelNumeral M 3673 → F pc ![s] ≠ modelNumeral M 10 →
    ∀ gap count : M, ∃ nextGap nextCount : M,
      F pc ![F step ![s]] < modelNumeral M 3673 ∧
      Reach1 table (F sourceRootCode ![s,gap,count,spare])
        (F sourceRootCode ![F step ![s],nextGap,nextCount,spare]) := by
  classical
  intro s hbound hnormal gap count
  let s' : M := F step ![s]
  let a := tapeArgs s count spare
  let inc := incremented a count
  obtain ⟨i,hi,hpc,hregs⟩ := boundedStepCalibration s (regs s) hbound (by intro r; rfl)
  obtain ⟨instr,hinst,hc⟩ := atSite i.val (checks i.val i.isLt)
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
      exact stepAt s s' gap count spare count i j hi hpc' boxes none trivial false .none hc hout
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
      exact stepAt s s' gap count spare (count+1) i j hi hpc' boxes none trivial false _ hc hout
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
      exact stepAt s s' gap count spare count i j hi hpc' boxes _ hb false .none hzcheck hout
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
      exact stepAt s s' gap count spare count i j hi hpc' boxes _ hb true _ hpcheck hout

private theorem haltCertified : haltContract 10 512 = true := by decide +kernel

theorem terminal (spare : M) (boxes : Boxes spare) (s gap count : M)
    (hpc : F pc ![s] = modelNumeral M 10) :
    ∃ k : M, π₁ (ConPA.Machine.runFrom table k (F sourceRootCode ![s,gap,count,spare])) = (194 : M) := by
  let a := tapeArgs s count spare
  let box := boxValue a (incremented a count)
  obtain ⟨last, ⟨k, _, hrun⟩, hend⟩ := halt_sound gap (boxes s count none trivial) 10 512 haltCertified
  change ConPA.Machine.runFrom table k (root gap box 10) = last at hrun
  have hin : box (.plain .none) = F PA194RegisterPermutation.sourceFileCode (args s count spare) :=
    (frameFile s count spare).symm
  rw [root_initial_file, hin, ←sourceRoot_eval s gap count spare ⟨10,by decide⟩ hpc] at hrun
  exact ⟨k, by rw [hrun]; exact hend⟩

theorem halt_iff_controller (checks : AllContracts) (boxes : Boxes (PA194CompressedStartup.initialSpare (M := M))) :
    (∃ t : M, π₁ (ConPA.Machine.run table t) = (194 : M)) ↔
      ∃ n : M, F pc ![F run ![n,PA194CompressedStartup.initialSource]] = modelNumeral M 3674 := by
  refine PA194VariantController.halt_iff_controller table 194 sourceRootCode initialSource (58170 : M)
    initialSpare 0 (modelNumeral M 25) ?_ PA194ORInitializer.startup_root ?_ halt_absorbs ?_
    (terminal initialSpare boxes)
  · rw [initialPC]
    exact modelNumeralStrict 25 3673 (by decide)
  · intro s gap count hpc
    obtain ⟨i, hi⟩ := modelBelowNumeral 3673 (F pc ![s]) hpc
    rw [sourceRoot_eval s gap count _ i hi, root_control]
    norm_num
  · intro s gap count hs hn
    obtain ⟨nextGap, nextCount, hpc, k, hk, hrun⟩ := advance checks _ boxes s hs hn gap count
    exact ⟨k, nextGap, nextCount, hk, hpc, hrun⟩

#print axioms advance
#print axioms terminal
#print axioms literalBoxes
#print axioms halt_iff_controller
end models
end PA194ORController
