import BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252

/-!
Exact forward crossing of one unmarked unary register block
in the actual frozen252 arithmetic evaluator. All internal register values and
both complete numeric tape halves are arbitrary. Two literal rows precede the
already proved uniform one scan. The three public instantiations use actual
seek/probe numeric pairs43/59,72/82,84/96. No first-exit, absolute head, spare
invariant, or complete register/scheduler simulation is asserted.

This ports the forward_block/suffix_forward_block contracts in the maintained
RegisterBoxesPerm252, RegisterIncrementPerm252 and RegisterDecrementPerm252.
Those contracts derive from mira-emmy PR20 head
0d544f2a2e3c18f12278441a74b7879f31cbe856, ZF/m253/coq/tm/Box.v.
Mira-Cult, Jeff and Wade retain their machine, verification and framework
attributions. This is a new all-internal arithmetic proof on the frozen table.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive right-moving row retains its final write even when target=0. -/
lemma step_right_row (read write : Bool) (q target : V)
    (hrow : actionLookup q (digit read) = 4*target+3+digit write) (left suffix : V) :
    stepValue (frame q left (2*suffix+digit read)) =
      frame target (2*left+digit write) suffix := by
  have hn : 4*target+3+digit (V := V) write ≠ 0 := by
    rw [show (4*target+3+digit write : V) = (4*target+2+digit write)+1 by ring]
    simp
  unfold frame
  change genericStepValue actionLookup (cantor q (cantor left (2*suffix+digit read))) = _
  simp only [genericStepValue, first_cantor, second_cantor, digit_mod_two, hrow, if_neg hn]
  rw [apply_right, digit_div_two]
  rfl

/-- Fixed actual-table read/write/target data lift to every arithmetic model. -/
lemma right_transition_of_nat (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+3+write.toNat) :
    actionLookup (q : V) (digit read) = 4*(target : V)+3+digit write := by
  have h := actionLookup_numeral (V := V) q read.toNat
  rw [hrow] at h
  cases read <;> cases write <;> simpa [digit, numeral_eq_natCast] using h

lemma step_right_numeral (read write : Bool) (q target : Nat)
    (hrow : lookupNat literalRows 0 q read.toNat = 4*target+3+write.toNat) (left suffix : V) :
    stepValue (frame (q : V) left (2*suffix+digit read)) =
      frame (target : V) (2*left+digit write) suffix :=
  step_right_row read write (q : V) (target : V)
    (right_transition_of_nat read write q target hrow) left suffix

/-- Zero separator followed by value+1 ones, then the entire suffix. -/
noncomputable def registerBlock (value suffix : V) : V := 2*bitPrefix true (value+1) suffix
/-- The same crossed cells in nearest-first order on the left half. -/
noncomputable def reverseBlock (value left : V) : V := bitPrefix true (value+1) (2*left)

def registerBlockDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out value suffix. ∃ ones, !ArithmeticTapePrefix254.onesPrefixDef ones (value+1) suffix ∧ out = 2*ones”
def reverseBlockDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out value left. !ArithmeticTapePrefix254.onesPrefixDef out (value+1) (2*left)”
instance registerBlock_defined : 𝚺₁-Function₂[V] registerBlock via registerBlockDef :=
  .mk fun e => by simp [registerBlockDef, registerBlock, bitPrefix]
instance reverseBlock_defined : 𝚺₁-Function₂[V] reverseBlock via reverseBlockDef :=
  .mk fun e => by simp [reverseBlockDef, reverseBlock, bitPrefix]

lemma registerBlock_zero (suffix : V) : registerBlock 0 suffix = 4*suffix+2 := by
  unfold registerBlock
  rw [bitPrefix_succ, bitPrefix_zero]
  simp only [digit, if_true]
  ring

/-- Exactly value+2 represented steps, including both separator/header rows.
The suffix may itself begin with one; this theorem is an endpoint equality. -/
theorem forward_block (seek probe : V)
    (hseek0 : actionLookup seek (digit false) = 4*probe+3+digit false)
    (hprobe1 : actionLookup probe (digit true) = 4*seek+3+digit true)
    (hseek1 : actionLookup seek (digit true) = 4*seek+3+digit true)
    (value left suffix : V) :
    runFrom (value+2) (frame seek left (registerBlock value suffix)) =
      frame seek (reverseBlock value left) suffix := by
  have first : stepValue (frame seek left (registerBlock value suffix)) =
      frame probe (2*left) (bitPrefix true (value+1) suffix) := by
    simpa only [registerBlock, digit, Bool.false_eq_true, if_false, add_zero] using
      step_right_row false false seek probe hseek0 left (bitPrefix true (value+1) suffix)
  have second : stepValue (frame probe (2*left) (bitPrefix true (value+1) suffix)) =
      frame seek (2*(2*left)+digit true) (bitPrefix true value suffix) := by
    rw [bitPrefix_succ, step_right_row true true probe seek hprobe1]
  rw [show (value+2 : V) = (value+1)+1 by ring, runFrom_first, first,
    runFrom_first, second, scan_right true seek hseek1, bitPrefix_push]
  rfl

/-- Actual zero-decrement seek/probe states, Fin42/58. -/
theorem forward_dec (value left suffix : V) :
    runFrom (value+2) (frame 43 left (registerBlock value suffix)) =
      frame 43 (reverseBlock value left) suffix :=
  forward_block 43 59
    (right_transition_of_nat false false 43 59 (by decide))
    (right_transition_of_nat true true 59 43 (by decide))
    (right_transition_of_nat true true 43 43 (by decide)) value left suffix

/-- Actual increment seek/probe states, Fin71/81. -/
theorem forward_inc (value left suffix : V) :
    runFrom (value+2) (frame 72 left (registerBlock value suffix)) =
      frame 72 (reverseBlock value left) suffix :=
  forward_block 72 82
    (right_transition_of_nat false false 72 82 (by decide))
    (right_transition_of_nat true true 82 72 (by decide))
    (right_transition_of_nat true true 72 72 (by decide)) value left suffix

/-- Actual positive-decrement suffix seek/probe states, Fin83/95. -/
theorem forward_suffix (value left suffix : V) :
    runFrom (value+2) (frame 84 left (registerBlock value suffix)) =
      frame 84 (reverseBlock value left) suffix :=
  forward_block 84 96
    (right_transition_of_nat false false 84 96 (by decide))
    (right_transition_of_nat true true 96 84 (by decide))
    (right_transition_of_nat true true 84 84 (by decide)) value left suffix

end SetTheory.BusyBeaver.ZFC.ArithmeticRegisterForwardPerm252
