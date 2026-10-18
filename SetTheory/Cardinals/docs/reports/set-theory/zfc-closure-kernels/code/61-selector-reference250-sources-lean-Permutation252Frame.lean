import BusyBeaver.ZFC.RegisterBoxes253
import BusyBeaver.ZFC.RegisterPath

/-!
Register layout for the new 252-state permutation candidate.

The source table is the old-label runtime fold with physical permutation
`[0,3,4,5,8,1,6,2,7]`; its SHA-256 is
939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713.
The logical register semantics and all original program instructions are
unchanged. This module checks the new finite layout and defines a complete
dispatch representation, with arbitrary spare values and zero exterior.

The frame is generic in the binary state type and dispatch state. Therefore
it does not assume a relabeling theorem or the candidate's execution. The
exact blank bootstrap, program endpoint and general binary instruction
simulation remain separate interfaces.
-/

namespace SetTheory.BusyBeaver.ZFC.Permutation252Frame

open RegisterPath FiniteZipper

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Old physical index to the candidate physical index. -/
def physicalPermutation : List Nat := [0, 3, 4, 5, 8, 1, 6, 2, 7]

/-- Candidate physical position of each logical register, used only below 9. -/
def physOf : Nat → Nat
  | 0 => 6 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 3
  | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 1 | _ => 0

/-- Logical register stored at each candidate physical position. -/
def physicalOrder : List Nat := [2, 8, 1, 4, 3, 7, 0, 5, 6]

def vregs (R : Registers) : List Nat := physicalOrder.map R

theorem permutation_composition : ∀ r : Fin 9,
    physOf r.val = (physicalPermutation[
      ([6, 7, 0, 2, 1, 8, 4, 3, 5] : List Nat)[r.val]?.getD 0]?.getD 0) := by
  decide

theorem physOf_lt : ∀ r : Fin 9, physOf r.val < 9 := by decide

theorem physicalOrder_inverse : ∀ r : Fin 9,
    physicalOrder[physOf r.val]?.getD 9 = r.val := by decide

theorem physOf_inverse : ∀ p : Fin 9,
    physOf (physicalOrder[p.val]?.getD 9) = p.val := by decide

theorem physOf_injective : ∀ r s : Fin 9, physOf r.val = physOf s.val → r = s := by
  decide

theorem vregs_length (R : Registers) : (vregs R).length = 9 := rfl

private theorem nine_cases (r : Nat) (hr : r < 9) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 := by
  omega

/-- Every selected physical block is exactly its logical register. -/
theorem nth_vregs (R : Registers) (r : Nat) (hr : r < 9) :
    (vregs R)[physOf r]?.getD 0 = R r := by
  rcases nine_cases r hr with h | h | h | h | h | h | h | h | h
  all_goals subst r; rfl

/-- List replacement commutes with the exact logical-register update. -/
theorem update_vregs (R : Registers) (r value : Nat) (hr : r < 9) :
    writeRegisters (vregs R) (physOf r) value = vregs (update R r value) := by
  rcases nine_cases r hr with h | h | h | h | h | h | h | h | h
  all_goals subst r; rfl

/-- Arbitrary spare data is outside every selected primary block. -/
theorem nth_vregs_append (R : Registers) (spares : List Nat) (r : Nat) (hr : r < 9) :
    (vregs R ++ spares)[physOf r]?.getD 0 = R r := by
  rcases nine_cases r hr with h | h | h | h | h | h | h | h | h
  all_goals subst r; rfl

theorem update_vregs_append (R : Registers) (spares : List Nat)
    (r value : Nat) (hr : r < 9) :
    writeRegisters (vregs R ++ spares) (physOf r) value =
      vregs (update R r value) ++ spares := by
  rcases nine_cases r hr with h | h | h | h | h | h | h | h | h
  all_goals subst r; rfl

theorem increment_vregs (R : Registers) (r : Nat) (hr : r < 9) :
    writeRegisters (vregs R) (physOf r) ((vregs R)[physOf r]?.getD 0 + 1) =
      vregs (update R r (R r + 1)) := by
  rw [nth_vregs R r hr, update_vregs R r (R r + 1) hr]

theorem decrement_vregs (R : Registers) (r : Nat) (hr : r < 9) :
    writeRegisters (vregs R) (physOf r) ((vregs R)[physOf r]?.getD 0 - 1) =
      vregs (update R r (R r - 1)) := by
  rw [nth_vregs R r hr, update_vregs R r (R r - 1) hr]

def LogicalTailZero (R : Registers) : Prop := ∀ i : Nat, R (9 + i) = 0

theorem tail_update (R : Registers) (r value : Nat) (hr : r < 9)
    (ht : LogicalTailZero R) : LogicalTailZero (update R r value) := by
  intro i
  change (if 9 + i = r then value else R (9 + i)) = 0
  rw [if_neg (by omega)]
  exact ht i

/-- Blocks contain one separator and value+1 ones. All suffix data is retained. -/
def registerBits : List Nat → List Bool := RegisterBoxes253.registerBits

def dispatchZip {states : Nat} (dispatch : Fin states) (head : Int)
    (leftPadding rightPadding : Nat) (logical : Configuration)
    (gap : Nat) (spares : List Nat) : ZipConfig states :=
  { state := some dispatch, head := head,
    left := true :: List.replicate leftPadding false,
    right := logical.path ++ List.replicate gap false ++ [true] ++
      registerBits (vregs logical.registers ++ spares) ++
      List.replicate rightPadding false }

/-- A whole infinite tape, including the marker, PC, header and arbitrary spares.
No spare-zero or spare-capacity assumption is imposed. -/
def DispatchFrame {states : Nat} (dispatch : Fin states) (binary : Config states)
    (logical : Configuration) (gap : Nat) (spares : List Nat) : Prop :=
  40 ≤ logical.path.length + gap ∧ LogicalTailZero logical.registers ∧
    ∃ leftPadding rightPadding : Nat,
      ZipRep binary (dispatchZip dispatch binary.head leftPadding rightPadding logical gap spares)

def zeroRoot : Configuration := ⟨[], fun _ => 0⟩

theorem vregs_zero : vregs zeroRoot.registers = [0, 0, 0, 0, 0, 0, 0, 0, 0] := rfl

theorem zeroRoot_tail : LogicalTailZero zeroRoot.registers := fun _ => rfl

/-- This is the precise finite zipper shape required from the independent boot. -/
theorem zeroRoot_dispatchZip {states : Nat} (dispatch : Fin states) (head : Int)
    (leftPadding rightPadding gap : Nat) (spares : List Nat) :
    dispatchZip dispatch head leftPadding rightPadding zeroRoot gap spares =
      { state := some dispatch, head := head,
        left := true :: List.replicate leftPadding false,
        right := List.replicate gap false ++ [true] ++
          registerBits ([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ spares) ++
          List.replicate rightPadding false } := rfl

theorem frame_of_zeroRoot_zip {states : Nat} (dispatch : Fin states)
    (binary : Config states) (gap : Nat) (spares : List Nat)
    (hg : 40 ≤ gap) (leftPadding rightPadding : Nat)
    (hz : ZipRep binary
      (dispatchZip dispatch binary.head leftPadding rightPadding zeroRoot gap spares)) :
    DispatchFrame dispatch binary zeroRoot gap spares :=
  ⟨by simpa only [zeroRoot, List.length_nil, Nat.zero_add] using hg,
    zeroRoot_tail, leftPadding, rightPadding, hz⟩

end SetTheory.BusyBeaver.ZFC.Permutation252Frame
