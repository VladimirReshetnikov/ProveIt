import PA194HXControllerStepAt
import PA194HXContractSound
import PA194SourceHaltUnique
import PA194SourceBoundedStep
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194HXControllerAdvance
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion TableDispatch PA194StateOne PA194FiniteControls
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceBoundedStep
open PA194SourcePCBound (pcModel)
open PA194SourceInstructionCalibration PA194SourceRegisterRelation PA194SourceHaltUnique
open PA194CompressedSourceFrame PA194HXSourceArgs PA194HXControllerStepAt
open PA194CompressedSourceArgs (regs)
open PA194CompressedBoxOracle PA194CompressedBoxFiles PA194CompressedIncrementOracle
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime
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

private theorem destination_eq (o : Option Nat) : destination o = o.getD 0 := by
  cases o <;> rfl

def AllContracts : Prop := ∀ i : Nat, i < 3673 → PA194HXContracts.checkAt i = true

/-- Every nonterminal source instruction advances the literal machine after
a positive model-valued number of steps. Each finite contract is attached to
the actual instruction read from the checked source tree. -/
theorem advance (checks : AllContracts) (spare : M) :
    ∀ s : M, F pc ![s] < modelNumeral M 3673 → F pc ![s] ≠ modelNumeral M 10 →
    ∀ gap count : M, ∃ nextGap nextCount : M,
      F pc ![F step ![s]] < modelNumeral M 3673 ∧
      Reach1 PA194HXDispatch.table (F PA194HXSourceRoot.sourceRootCode ![s,gap,count,spare])
        (F PA194HXSourceRoot.sourceRootCode ![F step ![s],nextGap,nextCount,spare]) := by
  classical
  intro s hbound hnormal gap count
  let s' : M := F step ![s]
  let a := tapeArgs s count spare
  let inc := incremented a count
  obtain ⟨i,hi,hpc,hregs⟩ := boundedStepCalibration s (regs s) hbound (by intro r; rfl)
  obtain ⟨instr,hinst,hc⟩ := PA194HXContractSound.atSite i.val (checks i.val i.isLt)
  have ht : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie i.val).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some instr := by
    rwa [←PA194SourceProgram.resolve_tree]
  rw [ht] at hpc hregs
  have hl : regs s' = (execute (some instr) (regs s)).2 := funext hregs
  have hpc' : F pc ![s'] = modelNumeral M (execute (some instr) (regs s)).1 :=
    (pcModel s').trans hpc
  have bslot (r : Fin 9) : PA194HXContracts.physicalRegister r < 9 := (PA194HXAllocation.hx r).isLt
  have read (r : Fin 9) : a (slot (position r)) = regs s r := readRegister s count spare r
  cases instr with
  | halt =>
    exfalso
    exact hnormal (by rwa [resolvedHaltIndex i.val hinst] at hi)
  | jump next =>
    obtain ⟨hb,hc⟩ := hc
    rw [← destination_eq next] at hb hc
    let j : Fin 3673 := ⟨destination next,hb⟩
    refine ⟨gap,count,?_,?_⟩
    · rw [hpc']
      exact modelNumeralStrict _ _ hb
    · have hout : boxValue a inc (.plain .none) = file (tapeArgs s' count spare) := by
        rw [sameRegisters s s' count spare hl]
        rfl
      exact stepAt s s' gap count spare count i j hi hpc' none trivial false .none hc hout
  | inc r next =>
    obtain ⟨hb,hc⟩ := hc
    rw [← destination_eq next] at hb hc
    let j : Fin 3673 := ⟨destination next,hb⟩
    refine ⟨gap,count+1,?_,?_⟩
    · rw [hpc']
      exact modelNumeralStrict _ _ hb
    · have hout : boxValue a inc (.plain (.inc (PA194HXContracts.physicalRegister r))) =
          file (tapeArgs s' (count+1) spare) := by
        rw [incrementRegisters s s' count spare r hl]
        simp only [boxValue,bslot r,dite_true,inc,position]
        rfl
      exact stepAt s s' gap count spare (count+1) i j hi hpc' none trivial false
        (.inc (PA194HXContracts.physicalRegister r)) hc hout
  | dec r zero positive =>
    obtain ⟨hzbound,hpbound,hzcheck,hpcheck⟩ := hc
    rw [← destination_eq zero] at hzbound hzcheck
    rw [← destination_eq positive] at hpbound hpcheck
    by_cases hz : regs s r = (0 : M)
    · simp only [execute,hz,if_true] at hpc' hl
      let j : Fin 3673 := ⟨destination zero,hzbound⟩
      have hzbr : BranchOK a (some (PA194HXContracts.physicalRegister r,true)) := by
        intro hr
        change a (slot (position r)) = 0
        rw [read r,hz]
      refine ⟨gap,count,by rw [hpc']; exact modelNumeralStrict _ _ hzbound,?_⟩
      have hout : boxValue a inc (.plain .none) = file (tapeArgs s' count spare) := by
        rw [sameRegisters s s' count spare hl]
        rfl
      exact stepAt s s' gap count spare count i j hi hpc' _ hzbr false .none hzcheck hout
    · simp only [execute,hz,if_false] at hpc' hl
      let j : Fin 3673 := ⟨destination positive,hpbound⟩
      have hpbr : BranchOK a (some (PA194HXContracts.physicalRegister r,false)) := by
        intro hr
        change a (slot (position r)) ≠ 0
        rw [read r]
        exact hz
      refine ⟨gap+1,count,by rw [hpc']; exact modelNumeralStrict _ _ hpbound,?_⟩
      have hout : boxValue a inc (.plain (.dec (PA194HXContracts.physicalRegister r))) =
          file (tapeArgs s' count spare) := by
        rw [updatedRegisters s s' count spare _ r hl]
        simp only [boxValue,bslot r,dite_true,decrement,←read r,position]
        rfl
      exact stepAt s s' gap count spare count i j hi hpc' _ hpbr true
        (.dec (PA194HXContracts.physicalRegister r)) hpcheck hout

#print axioms advance
end models
end PA194HXControllerAdvance
