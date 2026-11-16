import PA194RegisterControllerStep
import PA194SourceHaltUnique
import PA194SourceBoundedStep
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194RegisterControllerAdvance
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion TableDispatch PA194StateOne PA194FiniteControls
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceBoundedStep
open PA194SourcePCBound (pcModel)
open PA194SourceInstructionCalibration PA194SourceRegisterRelation PA194SourceHaltUnique
open PA194CompressedSourceFrame PA194RegisterLayout PA194RegisterControllerStep
open PA194RegisterContracts
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

def AllContracts (A : Allocation) (machine : M6.Zip.TMN) : Prop :=
  ∀ i : Nat, i < 3673 → checkAt A machine i = true

/-- Every nonterminal source instruction advances the literal machine after
a positive model-valued number of steps. Each finite contract is attached to
the actual instruction read from the checked source tree. -/
theorem advance (A : Allocation) {T : Table} {machine : M6.Zip.TMN} {label : Nat → Nat}
    (rows : RowAgreement T machine label) (control : label 84 = 24)
    (boxes : Boxes (M := M) T label) (checks : AllContracts A machine) (spare : M) :
    ∀ s : M, F pc ![s] < modelNumeral M 3673 → F pc ![s] ≠ modelNumeral M 10 →
    ∀ gap count : M, ∃ nextGap nextCount : M,
      F pc ![F step ![s]] < modelNumeral M 3673 ∧
      Reach1 T (F (PA194RegisterRoot.sourceRootCode A) ![s,gap,count,spare])
        (F (PA194RegisterRoot.sourceRootCode A) ![F step ![s],nextGap,nextCount,spare]) := by
  classical
  intro s hbound hnormal gap count
  let s' : M := F step ![s]
  let a := tapeArgs A s count spare
  let inc := incremented a count
  obtain ⟨i,hi,hpc,hregs⟩ := boundedStepCalibration s (regs s) hbound (by intro r; rfl)
  obtain ⟨instr,hinst,hc⟩ := atSite A machine i.val (checks i.val i.isLt)
  have ht : (M6.Source.PathTrie.nthSite PA194.SourceTree.trie i.val).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some instr := by
    rwa [←PA194SourceProgram.resolve_tree]
  rw [ht] at hpc hregs
  have hl : regs s' = (execute (some instr) (regs s)).2 := funext hregs
  have hpc' : F pc ![s'] = modelNumeral M (execute (some instr) (regs s)).1 :=
    (pcModel s').trans hpc
  have bslot (r : Fin 9) : physicalRegister A r < 9 := (A.position r).isLt
  have read (r : Fin 9) : a (slot (A.position r)) = regs s r := readRegister A s count spare r
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
    · have hout : boxValue a inc (.plain .none) = file (tapeArgs A s' count spare) := by
        rw [sameRegisters A s s' count spare hl]
        rfl
      exact stepAt A rows control boxes s s' gap count spare count i j hi hpc' none trivial false .none hc hout
  | inc r next =>
    obtain ⟨hb,hc⟩ := hc
    rw [← destination_eq next] at hb hc
    let j : Fin 3673 := ⟨destination next,hb⟩
    refine ⟨gap,count+1,?_,?_⟩
    · rw [hpc']
      exact modelNumeralStrict _ _ hb
    · have hout : boxValue a inc (.plain (.inc (physicalRegister A r))) =
          file (tapeArgs A s' (count+1) spare) := by
        rw [incrementRegisters A s s' count spare r hl, boxValue, dif_pos (bslot r)]
        rfl
      exact stepAt A rows control boxes s s' gap count spare (count+1) i j hi hpc' none trivial false
        (.inc (physicalRegister A r)) hc hout
  | dec r zero positive =>
    obtain ⟨hzbound,hpbound,hzcheck,hpcheck⟩ := hc
    rw [← destination_eq zero] at hzbound hzcheck
    rw [← destination_eq positive] at hpbound hpcheck
    by_cases hz : regs s r = (0 : M)
    · simp only [execute,hz,if_true] at hpc' hl
      let j : Fin 3673 := ⟨destination zero,hzbound⟩
      have hzbr : BranchOK a (some (physicalRegister A r,true)) := by
        intro hr
        change a (slot (A.position r)) = 0
        rw [read r,hz]
      refine ⟨gap,count,by rw [hpc']; exact modelNumeralStrict _ _ hzbound,?_⟩
      have hout : boxValue a inc (.plain .none) = file (tapeArgs A s' count spare) := by
        rw [sameRegisters A s s' count spare hl]
        rfl
      exact stepAt A rows control boxes s s' gap count spare count i j hi hpc' _ hzbr false .none hzcheck hout
    · simp only [execute,hz,if_false] at hpc' hl
      let j : Fin 3673 := ⟨destination positive,hpbound⟩
      have hpbr : BranchOK a (some (physicalRegister A r,false)) := by
        intro hr
        change a (slot (A.position r)) ≠ 0
        rw [read r]
        exact hz
      refine ⟨gap+1,count,by rw [hpc']; exact modelNumeralStrict _ _ hpbound,?_⟩
      have hout : boxValue a inc (.plain (.dec (physicalRegister A r))) =
          file (tapeArgs A s' count spare) := by
        rw [updatedRegisters A s s' count spare _ r hl, boxValue, dif_pos (bslot r)]
        simp only [decrement, ←read r, physicalRegister]
        rfl
      exact stepAt A rows control boxes s s' gap count spare count i j hi hpc' _ hpbr true
        (.dec (physicalRegister A r)) hpcheck hout

#print axioms advance
end models
end PA194RegisterControllerAdvance
