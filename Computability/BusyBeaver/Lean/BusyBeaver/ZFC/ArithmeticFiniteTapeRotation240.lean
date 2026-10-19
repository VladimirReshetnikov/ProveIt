import BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240
import BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240

set_option autoImplicit false

/-!
Finite-data compatibility for the Rotation240 tape interpretation. Only the
bit lists, register lists and repetition counts in these adapters are external
natural data; each untouched numeric suffix is an arbitrary internal value.
The identities connect existing numeric encodings without running a machine.
The proofs follow the pure codec lemmas of ArithmeticSiteBootPerm252 while
avoiding its old machine/box/runtime interfaces. Original machine and framework
attribution of Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt is retained.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachinePerm252
open ArithmeticMachineStepPerm252 (encodeConfig)
open ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticOneRegisterBlocksRotation240 ArithmeticCarryTraversalRotation240
open RegisterBoxesPerm252 (registerBits)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def bitsPrefix : List Bool → V → V
  | [], suffix => suffix
  | b :: bs, suffix => 2*bitsPrefix bs suffix+digit b

theorem bitsPrefix_append (xs ys : List Bool) (suffix : V) :
    bitsPrefix (xs++ys) suffix = bitsPrefix xs (bitsPrefix ys suffix) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append, bitsPrefix, ih]

theorem bitPrefix_replicate (b : Bool) (n : Nat) (suffix : V) :
    bitPrefix b (n : V) suffix = bitsPrefix (List.replicate n b) suffix := by
  induction n with
  | zero => simp only [Nat.cast_zero, bitPrefix_zero, List.replicate_zero, bitsPrefix]
  | succ n ih =>
    simp only [Nat.cast_succ, bitPrefix_succ, List.replicate_succ, bitsPrefix, ih]

theorem bitsCode_cast (xs : List Bool) : (bitsCode xs : V) = bitsPrefix xs 0 := by
  induction xs with
  | nil => simp [bitsCode, bitsPrefix]
  | cons b xs ih =>
    cases b <;> simp only [bitsCode, bitsPrefix, Bool.toNat_false, Bool.toNat_true,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, digit,
      Bool.false_eq_true, if_true, if_false, ih] <;> ring

theorem registerBlock_nat (v : Nat) (suffix : V) :
    registerBlock (v : V) suffix =
      bitsPrefix (false::true::List.replicate v true) suffix := by
  rw [registerBlock, bitPrefix_succ, bitPrefix_replicate]
  simp only [bitsPrefix, digit, Bool.false_eq_true, if_true, if_false]
  ring

theorem fileTape_nat (values : List Nat) (suffix : V) :
    fileTape (values.map (fun n : Nat => (n : V))) suffix =
      bitsPrefix (registerBits values) suffix := by
  induction values with
  | nil => rfl
  | cons v values ih =>
    change registerBlock (v : V) (fileTape (values.map (fun n : Nat => (n : V))) suffix) =
      bitsPrefix ((false::true::List.replicate v true) ++ registerBits values) suffix
    rw [bitsPrefix_append, ←registerBlock_nat, ih]

theorem oneBlocks_nat (n : Nat) (suffix : V) :
    oneBlocks (n : V) suffix = fileTape (List.replicate n (1 : V)) suffix := by
  induction n with
  | zero => simp only [Nat.cast_zero, oneBlocks_zero, List.replicate_zero, fileTape]
  | succ n ih =>
    simp only [Nat.cast_succ, oneBlocks_succ, List.replicate_succ,
      fileTape, registerBlock_one, ih]

/-- Keep the numeral transport generic rather than unfold a large boot code. -/
theorem cantor_cast (a b : Nat) : cantor (a : V) (b : V) = (Code254.P a b : V) := by
  symm
  apply cantor_graph.mpr
  have h := congrArg (fun n : Nat => (n : V))
    ((codeP_graph (Code254.P a b) a b).mp rfl)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h

theorem encodeConfig_cast (u : NumericConfig) :
    (encodeConfig u : V) = frame (u.state : V) (u.left : V) (u.right : V) := by
  simp only [encodeConfig, frame, cantor_cast]

end SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240
