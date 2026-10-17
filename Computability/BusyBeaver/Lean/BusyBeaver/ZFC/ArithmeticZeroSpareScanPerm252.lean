import BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254
import BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252

/-!
Arbitrary internal runs of unmarked zero register blocks in the actual
frozen252 arithmetic evaluator. The zero-block encoding and literal row
adapters follow the attributed Mira-Cult/Jeff/Wade register engine and the
ProveIt register permutation, as recorded in the imported modules.

Every count and both entire tape halves range over an arbitrary IΣ1 model.
No external finite-list assumption or first-exit assertion is used. This is a
numeric endpoint substrate, not the spare-growth invariant or the complete
register/scheduler simulation.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticZeroRegisterBlocks254
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same crossed zero blocks, now in nearest-first order on the left. -/
noncomputable def reverseZeroBlocks (count left : V) : V := zeroBlocks count (2*left) / 2

def reverseZeroBlocksDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out count left. ∃ raw, !zeroBlocksDef raw count (2*left) ∧ !divDef out raw 2”
instance reverseZeroBlocks_defined :
    𝚺₁-Function₂[V] reverseZeroBlocks via reverseZeroBlocksDef :=
  .mk fun e => by simp [reverseZeroBlocksDef, reverseZeroBlocks]
instance reverseZeroBlocks_definable : 𝚺₁-Function₂[V] reverseZeroBlocks :=
  reverseZeroBlocks_defined.to_definable
private instance reverseZeroBlocks_delta : 𝚫₁-Function₂[V] reverseZeroBlocks :=
  reverseZeroBlocks_defined.graph_delta.to_definable
private instance zeroBlocks_delta : 𝚫₁-Function₂[V] zeroBlocks :=
  zeroBlocks_defined_delta.to_definable
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom :=
  runFrom_defined_delta.to_definable
private instance frame_delta : 𝚫₁-Function₃[V] frame :=
  frame_defined.graph_delta.to_definable

/-- Evenness holds also at count0, where the complete old left half remains. -/
theorem zeroBlocks_even (count left : V) :
    ∃ half : V, zeroBlocks count (2*left) = 2*half := by
  induction count using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨left, by simp⟩
  case succ count _ih =>
    refine ⟨2*zeroBlocks count (2*left)+1, ?_⟩
    rw [zeroBlocks_succ]
    ring

theorem two_reverseZeroBlocks (count left : V) :
    2*reverseZeroBlocks count left = zeroBlocks count (2*left) := by
  obtain ⟨half, hh⟩ := zeroBlocks_even count left
  unfold reverseZeroBlocks
  rw [hh, even_div_two]

@[simp] theorem reverseZeroBlocks_zero (left : V) : reverseZeroBlocks 0 left = left := by
  simp [reverseZeroBlocks]

theorem reverseZeroBlocks_succ (count left : V) :
    reverseZeroBlocks (count+1) left = 4*reverseZeroBlocks count left+1 := by
  change zeroBlocks (count+1) (2*left)/2 = _
  rw [zeroBlocks_succ]
  have he : (4*zeroBlocks count (2*left)+2 : V) =
      2*(2*zeroBlocks count (2*left)+1) := by ring
  rw [he, even_div_two, ←two_reverseZeroBlocks count left]
  ring

theorem reverseZeroBlocks_push (count left : V) :
    reverseZeroBlocks count (4*left+1) = reverseZeroBlocks (count+1) left := by
  change zeroBlocks count (2*(4*left+1))/2 = zeroBlocks (count+1) (2*left)/2
  rw [show (2*(4*left+1) : V) = 4*(2*left)+2 by ring, zeroBlocks_push]

theorem reverseBlock_zero (left : V) : reverseBlock 0 left = 4*left+1 := by
  unfold reverseBlock
  rw [bitPrefix_succ, bitPrefix_zero]
  simp only [digit, if_true]
  ring

/-- The universal tape halves make this a Π1 induction predicate. -/
def ZeroBlockScan (q count : V) : Prop := ∀ left suffix : V,
  runFrom (2*count) (frame q left (zeroBlocks count suffix)) =
    frame q (reverseZeroBlocks count left) suffix
private instance zeroBlockScan_definable (q : V) : 𝚷₁-Predicate (ZeroBlockScan q) := by
  unfold ZeroBlockScan
  definability

/-- Complete crossing of an internally long zero-spare tail.
The three row equations refer to the actual lookup, not an abstract machine. -/
theorem scan_zero_blocks (seek probe : V)
    (hseek0 : actionLookup seek (digit false) = 4*probe+3+digit false)
    (hprobe1 : actionLookup probe (digit true) = 4*seek+3+digit true)
    (hseek1 : actionLookup seek (digit true) = 4*seek+3+digit true)
    (count left suffix : V) :
    runFrom (2*count) (frame seek left (zeroBlocks count suffix)) =
      frame seek (reverseZeroBlocks count left) suffix := by
  have allCounts : ∀ count : V, ZeroBlockScan seek count := by
    intro count
    induction count using ISigma1.pi1_succ_induction
    · exact zeroBlockScan_definable seek
    case zero => intro left suffix; simp
    case succ count ih =>
      intro left suffix
      have firstBlock :
          runFrom 2 (frame seek left (4*zeroBlocks count suffix+2)) =
            frame seek (4*left+1) (zeroBlocks count suffix) := by
        simpa only [zero_add, registerBlock_zero, reverseBlock_zero] using
          forward_block seek probe hseek0 hprobe1 hseek1 (0 : V) left
            (zeroBlocks count suffix)
      rw [show (2*(count+1) : V) = 2+2*count by ring, zeroBlocks_succ,
        runFrom_add, firstBlock, ih, reverseZeroBlocks_push]
  exact allCounts count left suffix

/-- Actual zero-decrement seek/probe pair, numeric43/59. -/
theorem scan_zero_blocks_dec (count left suffix : V) :
    runFrom (2*count) (frame 43 left (zeroBlocks count suffix)) =
      frame 43 (reverseZeroBlocks count left) suffix :=
  scan_zero_blocks 43 59
    (right_transition_of_nat false false 43 59 (by decide))
    (right_transition_of_nat true true 59 43 (by decide))
    (right_transition_of_nat true true 43 43 (by decide)) count left suffix

/-- Actual increment seek/probe pair, numeric72/82. -/
theorem scan_zero_blocks_inc (count left suffix : V) :
    runFrom (2*count) (frame 72 left (zeroBlocks count suffix)) =
      frame 72 (reverseZeroBlocks count left) suffix :=
  scan_zero_blocks 72 82
    (right_transition_of_nat false false 72 82 (by decide))
    (right_transition_of_nat true true 82 72 (by decide))
    (right_transition_of_nat true true 72 72 (by decide)) count left suffix

/-- Actual positive-decrement suffix seek/probe pair, numeric84/96. -/
theorem scan_zero_blocks_suffix (count left suffix : V) :
    runFrom (2*count) (frame 84 left (zeroBlocks count suffix)) =
      frame 84 (reverseZeroBlocks count left) suffix :=
  scan_zero_blocks 84 96
    (right_transition_of_nat false false 84 96 (by decide))
    (right_transition_of_nat true true 96 84 (by decide))
    (right_transition_of_nat true true 84 84 (by decide)) count left suffix

end SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252
