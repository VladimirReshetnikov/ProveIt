import BusyBeaver.ZFC.RegisterMarkPerm252

/-!
Instantiated from RegisterIncrement253.lean for the new permutation252 table.
Source SHA256: b67184c1ed66c2d7f08502695f8f35cc6f04137fea695c231a7316035dfc52d3.
The proof bodies are retained; all named states are independently relocated
using their original labels. Every row theorem must be checked on the new table.

Incrementing a marked unary register in the actual permutation252 machine.
Adapted from `shift_inc` and `box_inc` in mira-emmy's public PR20 head
0d544f2a2e3c18f12278441a74b7879f31cbe856, `ZF/m253/coq/tm/Box.v`.
The Mira-Cult/Jeff machine and Wade framework retain their attribution.
The suffix-shift proof covers arbitrary following register and spare data.
This excursion stops before the dispatcher updates the program counter.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterIncrementPerm252

open FiniteZipper ZipperRuns RegisterBoxesPerm252

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def seekInc : Fin 252 := ⟨71, by decide⟩ -- old73
def probeInc : Fin 252 := ⟨81, by decide⟩ -- old83
def shiftInc : Fin 252 := ⟨93, by decide⟩ -- old95
def shiftProbe : Fin 252 := ⟨107, by decide⟩ -- old109
def incReturnOnes : Fin 252 := ⟨62, by decide⟩ -- old63
def incReturnZero : Fin 252 := ⟨47, by decide⟩ -- old48

theorem row_seek_zero :
    machinePerm252.transition seekInc false = ⟨false, .right, some probeInc⟩ := by decide
theorem row_seek_one :
    machinePerm252.transition seekInc true = ⟨true, .right, some seekInc⟩ := by decide
theorem row_probe_one :
    machinePerm252.transition probeInc true = ⟨true, .right, some seekInc⟩ := by decide
theorem row_probe_zero :
    machinePerm252.transition probeInc false = ⟨true, .right, some shiftInc⟩ := by decide
theorem row_shift_one :
    machinePerm252.transition shiftInc true = ⟨true, .right, some shiftInc⟩ := by decide
theorem row_shift_zero :
    machinePerm252.transition shiftInc false = ⟨true, .right, some shiftProbe⟩ := by decide
theorem row_shift_probe_one :
    machinePerm252.transition shiftProbe true = ⟨false, .right, some shiftInc⟩ := by decide
theorem row_shift_probe_zero :
    machinePerm252.transition shiftProbe false = ⟨false, .left, some incReturnOnes⟩ := by decide
theorem row_return_one :
    machinePerm252.transition incReturnOnes true = ⟨true, .left, some incReturnOnes⟩ := by decide
theorem row_return_zero :
    machinePerm252.transition incReturnOnes false = ⟨false, .left, some incReturnZero⟩ := by decide
theorem row_return_probe :
    machinePerm252.transition incReturnZero true = ⟨true, .left, some incReturnOnes⟩ := by decide

theorem forward_block (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machinePerm252 (zAt seekInc h l (false :: true :: (List.replicate v true ++ X)))
      (v + 2) =
    zAt seekInc (h + ((v + 2 : Nat) : Int))
      (List.replicate v true ++ true :: false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ row_seek_zero, zipRun_first,
    step_right _ _ _ _ _ _ _ _ row_probe_one, scan_right _ _ _ row_seek_one]
  congr 1
  omega

theorem forward_file (pre : List Nat) (h : Int) (l X : List Bool) :
    zipRun machinePerm252 (zAt seekInc h l (registerBits pre ++ X)) (width pre) =
      zAt seekInc (h + (width pre : Int)) ((registerBits pre).reverse ++ l) X := by
  induction pre generalizing h l with
  | nil => simp [registerBits, width, zipRun]
  | cons v pre ih =>
    simp only [width, registerBits, List.cons_append, List.append_assoc]
    rw [zipRun_add, forward_block, ih]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.singleton_append]
    congr 1
    omega

private theorem ones_snoc (v : Nat) (l : List Bool) :
    List.replicate v true ++ true :: l = true :: (List.replicate v true ++ l) := by
  calc
    _ = (List.replicate v true ++ [true]) ++ l := (List.append_assoc _ _ _).symm
    _ = _ := by rw [← List.replicate_succ', List.replicate_succ]; rfl

theorem shift_separator_steps (h : Int) (l X : List Bool) :
    zipRun machinePerm252 (zAt shiftInc h l (false :: true :: X)) 2 =
      zAt shiftInc (h + 2) (false :: true :: l) X := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_shift_zero,
    zipRun_first, step_right _ _ _ _ _ _ _ _ row_shift_probe_one]
  simp only [zipRun]
  congr 1
  omega

/-- Carry the added one through an arbitrary register suffix, preserving
every suffix value and extending the complete finite file by one cell. -/
theorem shift_suffix (rest : List Nat) (a : Nat) (h : Int) (l : List Bool) :
    zipRun machinePerm252
      (zAt shiftInc h l (List.replicate a true ++ (registerBits rest ++ [false])))
      (a + width rest + 2) =
    leftAt incReturnOnes (h + ((a + width rest + 1 : Nat) : Int))
      ((List.replicate (a + 1) true ++ registerBits rest).reverse ++ l) [false] := by
  induction rest generalizing a h l with
  | nil =>
    simp only [width, registerBits, Nat.add_zero, List.append_nil, List.nil_append]
    rw [zipRun_add _ _ a 2, scan_right _ _ _ row_shift_one,
      zipRun_first, step_right _ _ _ _ _ _ _ _ row_shift_zero]
    have last (h' : Int) (l' : List Bool) :
        zipStep machinePerm252 (zAt shiftProbe h' l' []) =
          leftAt incReturnOnes h' l' [false] := by
      simp [zipStep, zAt, leftAt, zipWrite, zipLeft, row_shift_probe_zero]
    simp only [zipRun]
    rw [last]
    rw [List.reverse_replicate, List.replicate_succ]
    congr 1
    omega
  | cons m rest ih =>
    simp only [width, registerBits, List.cons_append, List.append_assoc]
    rw [show a + (m + 2 + width rest) + 2 = a + (2 + (m + width rest + 2)) by omega,
      zipRun_add, scan_right _ _ _ row_shift_one, zipRun_add,
      shift_separator_steps, ih]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.singleton_append, List.append_assoc, List.replicate_succ]
    simp only [ones_snoc, List.cons_append, List.nil_append]
    congr 1
    omega

theorem restore_mark (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machinePerm252 (zAt seekInc h l (false :: false :: (List.replicate v true ++ X))) 2 =
      zAt shiftInc (h + 2) (true :: false :: l) (List.replicate v true ++ X) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_seek_zero,
    zipRun_first, step_right _ _ _ _ _ _ _ _ row_probe_zero]
  simp only [zipRun]
  congr 1
  omega

/-- Increment the marked register, preserving the whole file and spare suffix.
The duration depends on the old file width, not on finite test bounds. -/
theorem increment_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool) :
    zipRun machinePerm252
      (zAt seekInc h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest ++ [false])))
      (2 * width (pre ++ v :: rest) + 3) =
      leftAt incReturnZero h l (registerBits (pre ++ (v + 1) :: rest) ++ [false]) := by
  have hne : pre ++ (v + 1) :: rest ≠ [] := by simp
  have firstCount : 2 * width (pre ++ v :: rest) + 3 =
      width pre + (2 + ((v + width rest + 2) + width (pre ++ (v + 1) :: rest))) := by
    simp only [width_append, width]
    omega
  rw [firstCount, zipRun_add, forward_file, zipRun_add]
  simp only [List.append_assoc]
  rw [restore_mark, zipRun_add, shift_suffix]
  have frame :
      (List.replicate (v + 1) true ++ registerBits rest).reverse ++
        true :: false :: ((registerBits pre).reverse ++ l) =
      (registerBits (pre ++ (v + 1) :: rest)).reverse ++ l := by
    simp only [registerBits_append, registerBits, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append]
  rw [frame, RegisterMarkPerm252.return_end machinePerm252 incReturnOnes incReturnZero
    row_return_one row_return_zero row_return_probe _ hne incReturnOnes row_return_one]
  congr 1
  simp only [width_append, width]
  omega

theorem increment {c : Config 252} (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt seekInc h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest ++ [false])))) :
    ZipRep (machinePerm252.runFrom c (2 * width (pre ++ v :: rest) + 3))
      (leftAt incReturnZero h l (registerBits (pre ++ (v + 1) :: rest) ++ [false])) := by
  have hs := zipRun_sound machinePerm252 (2 * width (pre ++ v :: rest) + 3) hc
  rw [increment_zip] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.RegisterIncrementPerm252
