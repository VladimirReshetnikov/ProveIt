import BusyBeaver.ZFC.RegisterIncrementPerm252

/-!
Instantiated from RegisterDecrement253.lean for the new permutation252 table.
Source SHA256: 29920971f0835fc7392df9c5e59d0561945acc74f972aed7a8c8c72b939f7a77.
The proof bodies are retained; all named states are independently relocated
using their original labels. Every row theorem must be checked on the new table.

Positive decrement in the actual permutation252 machine, including its new spare.

The contracts `shift_dec_block`, `shift_dec`, `Wf_rev` and `box_decp` are
attributed to mira-emmy PR20 head0d544f2a2e3c18f12278441a74b7879f31cbe856,
`ZF/m253/coq/tm/Box.v`. Mira-Cult designed the original machine, Jeff supplied
its verification, and Wade supplied the compiler framework. These are new
Lean proofs using the literal compact252 table and existing Core semantics.

Every preceding and following register value, spare suffix, integer head and
finite left context is arbitrary. The right exterior is blank. The output
decreases the positive target and appends a new zero-valued spare block.
PC updates and general dispatcher preservation are separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterDecrementPerm252

open FiniteZipper ZipperRuns RegisterBoxesPerm252

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def suffixSeek : Fin 252 := ⟨83, by decide⟩ -- old85
def suffixProbe : Fin 252 := ⟨95, by decide⟩ -- old97
def shiftLeft : Fin 252 := ⟨110, by decide⟩ -- old112
def shiftErase : Fin 252 := ⟨129, by decide⟩ -- old131

theorem row_test_one :
    machinePerm252.transition testDec true = ⟨true, .right, some suffixSeek⟩ := by decide
theorem row_suffix_one :
    machinePerm252.transition suffixSeek true = ⟨true, .right, some suffixSeek⟩ := by decide
theorem row_suffix_zero :
    machinePerm252.transition suffixSeek false = ⟨false, .right, some suffixProbe⟩ := by decide
theorem row_suffix_probe_one :
    machinePerm252.transition suffixProbe true = ⟨true, .right, some suffixSeek⟩ := by decide
theorem row_suffix_probe_zero :
    machinePerm252.transition suffixProbe false = ⟨false, .left, some shiftLeft⟩ := by decide
theorem row_shift_one :
    machinePerm252.transition shiftLeft true = ⟨true, .left, some shiftLeft⟩ := by decide
theorem row_shift_zero :
    machinePerm252.transition shiftLeft false = ⟨true, .left, some shiftErase⟩ := by decide
theorem row_erase_one :
    machinePerm252.transition shiftErase true = ⟨false, .left, some shiftLeft⟩ := by decide
theorem row_erase_zero :
    machinePerm252.transition shiftErase false =
      ⟨false, .left, some RegisterIncrementPerm252.incReturnOnes⟩ := by decide

private theorem ones_snoc (v : Nat) (l : List Bool) :
    List.replicate v true ++ true :: l = true :: (List.replicate v true ++ l) := by
  calc
    _ = (List.replicate v true ++ [true]) ++ l := (List.append_assoc _ _ _).symm
    _ = _ := by rw [← List.replicate_succ', List.replicate_succ]; rfl

theorem suffix_forward_block (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machinePerm252 (zAt suffixSeek h l (false :: true :: (List.replicate v true ++ X)))
      (v + 2) =
    zAt suffixSeek (h + ((v + 2 : Nat) : Int))
      (List.replicate v true ++ true :: false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ row_suffix_zero, zipRun_first,
    step_right _ _ _ _ _ _ _ _ row_suffix_probe_one, scan_right _ _ _ row_suffix_one]
  congr 1
  omega

theorem suffix_forward_file (rest : List Nat) (h : Int) (l X : List Bool) :
    zipRun machinePerm252 (zAt suffixSeek h l (registerBits rest ++ X)) (width rest) =
      zAt suffixSeek (h + (width rest : Int)) ((registerBits rest).reverse ++ l) X := by
  induction rest generalizing h l with
  | nil => simp [registerBits, width, zipRun]
  | cons v rest ih =>
    simp only [width, registerBits, List.cons_append, List.append_assoc]
    rw [zipRun_add, suffix_forward_block, ih]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.singleton_append]
    congr 1
    omega

theorem prepare_positive (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machinePerm252
      (zAt seekDec h l (false :: false :: true :: (List.replicate v true ++ X))) 3 =
      zAt suffixSeek (h + 3) (true :: false :: false :: l) (List.replicate v true ++ X) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_seek_zero,
    zipRun_first, step_right _ _ _ _ _ _ _ _ row_probe_zero,
    zipRun_first, step_right _ _ _ _ _ _ _ _ row_test_one]
  simp only [zipRun]
  congr 1
  omega

theorem prepare_shift (h : Int) (l : List Bool) :
    zipRun machinePerm252 (zAt suffixSeek h l [false, false]) 2 =
      zAt shiftLeft h l [false, false] := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_suffix_zero,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_suffix_probe_zero, leftAt_cons]
  simp only [zipRun]
  congr 1
  omega

/-- One block is shifted left; its value is retained and the two rightward
separator bits are accumulated explicitly. -/
theorem shift_block (v : Nat) (h : Int) (X Y : List Bool) :
    zipRun machinePerm252
      (zAt shiftLeft h (true :: (List.replicate v true ++ false :: X)) (false :: Y))
      (v + 2) =
      zAt shiftLeft (h - ((v + 2 : Nat) : Int)) X
        (false :: (List.replicate v true ++ false :: true :: Y)) := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_left _ _ _ _ _ _ _ _ row_shift_zero, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_erase_one,
    scan_left _ _ _ row_shift_one, leftAt_cons]
  congr 1
  omega

def rewoven : List Nat → List Bool → List Bool
  | [], Y => Y
  | v :: vs, Y => rewoven vs (List.replicate v true ++ false :: true :: Y)

theorem rewoven_append (a b : List Nat) (Y : List Bool) :
    rewoven (a ++ b) Y = rewoven b (rewoven a Y) := by
  induction a generalizing Y with
  | nil => rfl
  | cons v a ih => exact ih _

theorem rewoven_reverse (rest : List Nat) (Y : List Bool) :
    false :: true :: rewoven rest.reverse Y = registerBits rest ++ false :: true :: Y := by
  induction rest with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.reverse_cons, rewoven_append, rewoven, registerBits, List.cons_append]
    change false :: true :: (List.replicate v true ++
      (false :: true :: rewoven rest.reverse Y)) = _
    rw [ih]
    simp only [List.append_assoc]

theorem shift_blocks (rp : List Nat) (h : Int) (X Y : List Bool) :
    zipRun machinePerm252 (zAt shiftLeft h (leftBits rp ++ X) (false :: Y)) (width rp) =
      zAt shiftLeft (h - (width rp : Int)) X (false :: rewoven rp Y) := by
  induction rp generalizing h Y with
  | nil => simp [width, leftBits, rewoven, zipRun]
  | cons v rp ih =>
    simp only [leftBits, width, List.cons_append, List.append_assoc]
    rw [zipRun_add, shift_block, ih]
    simp only [rewoven]
    congr 1
    omega

theorem shift_file (rest : List Nat) (h : Int) (X Y : List Bool) :
    zipRun machinePerm252
      (zAt shiftLeft h ((registerBits rest).reverse ++ X) (false :: Y)) (width rest) =
      zAt shiftLeft (h - (width rest : Int)) X (false :: rewoven rest.reverse Y) := by
  simpa only [reverse_registerBits, width_reverse] using shift_blocks rest.reverse h X Y

theorem finish_shift (h : Int) (l Y : List Bool) :
    zipRun machinePerm252 (zAt shiftLeft h (false :: l) (false :: Y)) 2 =
      leftAt RegisterIncrementPerm252.incReturnOnes (h - 1) l (false :: true :: Y) := by
  rw [zipRun_first, step_left _ _ _ _ _ _ _ _ row_shift_zero, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_erase_zero]
  rfl

/-- The suffix operation appends a complete zero block rather than erasing
or treating that extra spare as a logical register. -/
theorem positive_tail_zip (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machinePerm252
      (zAt seekDec h l
        (false :: false :: (List.replicate (v + 1) true ++ registerBits rest ++ [false, false])))
      (2 * (v + width rest) + 9) =
      leftAt RegisterIncrementPerm252.incReturnOnes h l
        (registerBits (v :: (rest ++ [0])) ++ [false]) := by
  rw [show 2 * (v + width rest) + 9 =
      3 + (v + (width rest + (2 + (width rest + ((v + 2) + 2))))) by omega]
  simp only [List.replicate_succ, List.cons_append, List.append_assoc]
  rw [zipRun_add, prepare_positive, zipRun_add, scan_right _ _ _ row_suffix_one,
    zipRun_add, suffix_forward_file, zipRun_add, prepare_shift,
    zipRun_add, shift_file]
  rw [ones_snoc]
  rw [zipRun_add, shift_block, finish_shift]
  rw [rewoven_reverse]
  simp only [registerBits, registerBits_append, List.replicate_zero,
    List.nil_append, List.cons_append, List.append_assoc]
  congr 1
  omega

def positiveExit (pre : List Nat) : Fin 252 :=
  if pre = [] then RegisterIncrementPerm252.incReturnOnes else RegisterIncrementPerm252.incReturnZero

theorem positive_decrement_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool) :
    zipRun machinePerm252
      (zAt seekDec h l
        (registerBits pre ++ false :: false ::
          (List.replicate (v + 1) true ++ registerBits rest ++ [false, false])))
      (2 * width (pre ++ (v + 1) :: rest) + 3) =
      leftAt (positiveExit pre) h l (registerBits ((pre ++ v :: rest) ++ [0]) ++ [false]) := by
  have count : 2 * width (pre ++ (v + 1) :: rest) + 3 =
      width pre + ((2 * (v + width rest) + 9) + width pre) := by
    simp only [width_append, width]
    omega
  rw [count, zipRun_add, forward_file, zipRun_add, positive_tail_zip]
  by_cases he : pre = []
  · subst pre
    simp [width, registerBits, zipRun, positiveExit]
  · rw [RegisterMarkPerm252.return_end machinePerm252 RegisterIncrementPerm252.incReturnOnes
      RegisterIncrementPerm252.incReturnZero RegisterIncrementPerm252.row_return_one
      RegisterIncrementPerm252.row_return_zero RegisterIncrementPerm252.row_return_probe
      pre he RegisterIncrementPerm252.incReturnOnes RegisterIncrementPerm252.row_return_one]
    simp only [positiveExit, if_neg he, registerBits_append, registerBits,
      List.replicate_zero, List.nil_append, List.cons_append, List.append_assoc]
    congr 1
    omega

/-- Exterior false padding does not change any cell represented by a zipper. -/
theorem getD_append_false (l : List Bool) (i : Nat) :
    (l ++ [false]).getD i false = l.getD i false := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons b l ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem zipRep_pad_right {n : Nat} {c : Config n} {z : ZipConfig n} (hc : ZipRep c z) :
    ZipRep c { z with right := z.right ++ [false] } := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  intro i
  change Tape.read c.tape (z.head + (i : Int)) = (z.right ++ [false]).getD i false
  rw [getD_append_false]
  exact hc.2.2.2 i

/-- Actual Core positive decrement, with the same one-padding input format
as the other boxes and an extra zero spare in the whole output file. -/
theorem positive_decrement {c : Config 252} (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt seekDec h l
        (registerBits pre ++ false :: false ::
          (List.replicate (v + 1) true ++ registerBits rest ++ [false])))) :
    ZipRep (machinePerm252.runFrom c (2 * width (pre ++ (v + 1) :: rest) + 3))
      (leftAt (positiveExit pre) h l (registerBits ((pre ++ v :: rest) ++ [0]) ++ [false])) := by
  have padded := zipRep_pad_right hc
  have hp : ZipRep c
      (zAt seekDec h l
        (registerBits pre ++ false :: false ::
          (List.replicate (v + 1) true ++ registerBits rest ++ [false, false]))) := by
    simpa only [zAt, List.append_assoc, List.cons_append, List.nil_append] using padded
  have hs := zipRun_sound machinePerm252 (2 * width (pre ++ (v + 1) :: rest) + 3) hp
  rw [positive_decrement_zip] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.RegisterDecrementPerm252
