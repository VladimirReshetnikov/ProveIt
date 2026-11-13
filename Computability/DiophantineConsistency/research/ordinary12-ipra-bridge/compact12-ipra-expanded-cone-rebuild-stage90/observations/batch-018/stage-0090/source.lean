import BusyBeaver.ZFC.Table253
import BusyBeaver.ZFC.ZipperRuns

/-!
The zero-decrement register-file excursion of the actual public253 machine.

Adapted from mira-emmy's PR20 head 0d544f2a2e3c18f12278441a74b7879f31cbe856,
`ZF/m253/coq/tm/Box.v`, in particular `fwd`, `ret_file` and `box_dec0`.
The machine and original verification are attributed to Mira-Cult and Jeff;
Wade supplied the compiler framework. This is a new Lean proof using the
literal compact table, rather than an import of the upstream proof.

The erased first unary one marks the selected register. In particular, a
marked zero is two zeros, followed by the next block or exterior blank.
This convention differs from the frozen252 public-Wade backend's selector.

The theorem below covers arbitrary preceding register values, arbitrary
following blocks (including spares), arbitrary finite left context and the
whole zero-exterior tape. It stops at the box return state, before a PC update.
No general dispatch, enumerator or consistency theorem is asserted.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterBoxes253

open FiniteZipper ZipperRuns

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def seekDec : Fin 253 := ⟨79, by decide⟩ -- old43
def probeDec : Fin 253 := ⟨93, by decide⟩ -- old59
def testDec : Fin 253 := ⟨110, by decide⟩ -- old75
def restoreZero : Fin 253 := ⟨19, by decide⟩ -- old0
def returnOnes : Fin 253 := ⟨21, by decide⟩ -- old1
def returnZero : Fin 253 := ⟨23, by decide⟩ -- old3

theorem row_seek_zero :
    machine253.transition seekDec false = ⟨false, .right, some probeDec⟩ := by decide
theorem row_seek_one :
    machine253.transition seekDec true = ⟨true, .right, some seekDec⟩ := by decide
theorem row_probe_zero :
    machine253.transition probeDec false = ⟨false, .right, some testDec⟩ := by decide
theorem row_probe_one :
    machine253.transition probeDec true = ⟨true, .right, some seekDec⟩ := by decide
theorem row_test_zero :
    machine253.transition testDec false = ⟨false, .left, some restoreZero⟩ := by decide
theorem row_restore_zero :
    machine253.transition restoreZero false = ⟨true, .left, some returnOnes⟩ := by decide
theorem row_return_zero :
    machine253.transition returnOnes false = ⟨false, .left, some returnZero⟩ := by decide
theorem row_return_one :
    machine253.transition returnOnes true = ⟨true, .left, some returnOnes⟩ := by decide
theorem row_return_probe_one :
    machine253.transition returnZero true = ⟨true, .left, some returnOnes⟩ := by decide

/-- Each unmarked register is 0 followed by value+1 ones. -/
def registerBits : List Nat → List Bool
  | [] => []
  | v :: vs => false :: true :: (List.replicate v true ++ registerBits vs)

/-- The same blocks in the nearest-first order for the left half-tape. -/
def leftBits : List Nat → List Bool
  | [] => []
  | v :: vs => true :: (List.replicate v true ++ false :: leftBits vs)

def width : List Nat → Nat
  | [] => 0
  | v :: vs => v + 2 + width vs

theorem registerBits_eq_flatMap (vs : List Nat) :
    registerBits vs = vs.flatMap (fun v => false :: List.replicate (v + 1) true) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [registerBits, List.replicate_succ, ih]

theorem registerBits_append (a b : List Nat) :
    registerBits (a ++ b) = registerBits a ++ registerBits b := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [registerBits, ih]

theorem leftBits_append (a b : List Nat) :
    leftBits (a ++ b) = leftBits a ++ leftBits b := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [leftBits, ih]

theorem width_append (a b : List Nat) : width (a ++ b) = width a + width b := by
  induction a with
  | nil => simp [width]
  | cons v a ih => simp [width, ih, Nat.add_assoc]

theorem width_reverse (vs : List Nat) : width vs.reverse = width vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [width, width_append, ih]; omega

private theorem ones_snoc (v : Nat) (l : List Bool) :
    List.replicate v true ++ true :: l = true :: (List.replicate v true ++ l) := by
  calc
    _ = (List.replicate v true ++ [true]) ++ l := (List.append_assoc _ _ _).symm
    _ = _ := by rw [← List.replicate_succ', List.replicate_succ]; rfl

theorem reverse_registerBits (vs : List Nat) :
    (registerBits vs).reverse = leftBits vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [registerBits, List.reverse_append, ih, leftBits_append, leftBits,
      ones_snoc]

theorem width_eq_length (vs : List Nat) : width vs = (registerBits vs).length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [width, registerBits, ih]; omega

/-- Seek crosses a complete ordinary block without changing it. -/
theorem forward_block (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machine253 (zAt seekDec h l (false :: true :: (List.replicate v true ++ X)))
      (v + 2) =
    zAt seekDec (h + ((v + 2 : Nat) : Int))
      (List.replicate v true ++ true :: false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ row_seek_zero, zipRun_first,
    step_right _ _ _ _ _ _ _ _ row_probe_one, scan_right _ _ _ row_seek_one]
  congr 1
  omega

/-- Exact forward seek over an arbitrary unary register prefix. -/
theorem forward_file (pre : List Nat) (h : Int) (l X : List Bool) :
    zipRun machine253 (zAt seekDec h l (registerBits pre ++ X)) (width pre) =
      zAt seekDec (h + (width pre : Int)) ((registerBits pre).reverse ++ l) X := by
  induction pre generalizing h l with
  | nil => simp [registerBits, width, zipRun]
  | cons v pre ih =>
    simp only [width, registerBits, List.cons_append, List.append_assoc]
    rw [zipRun_add, forward_block, ih]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.singleton_append]
    congr 1
    omega

/-- Return across the whole prefix, expressed in nearest-block-first order. -/
theorem return_file_left (rp : List Nat) (h : Int) (l Y : List Bool) :
    zipRun machine253
      (zAt returnOnes h (leftBits rp ++ l) (false :: Y)) (width rp + 1) =
    leftAt returnZero (h - (width rp : Int)) l
      (registerBits rp.reverse ++ false :: Y) := by
  induction rp generalizing h Y with
  | nil =>
    simpa [width, leftBits, registerBits, zipRun] using
      step_left machine253 returnOnes returnZero false false h l Y row_return_zero
  | cons v rp ih =>
    simp only [width, leftBits, List.cons_append, List.append_assoc]
    rw [show v + 2 + width rp + 1 = (v + 2) + (width rp + 1) by omega, zipRun_add]
    have first :
        zipRun machine253
          (zAt returnOnes h (true :: (List.replicate v true ++ false :: (leftBits rp ++ l)))
            (false :: Y)) (v + 2) =
        zAt returnOnes (h - ((v + 2 : Nat) : Int)) (leftBits rp ++ l)
          (false :: (List.replicate v true ++ true :: false :: Y)) := by
      rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
        step_left _ _ _ _ _ _ _ _ row_return_zero, leftAt_cons, zipRun_first,
        step_left _ _ _ _ _ _ _ _ row_return_probe_one,
        scan_left _ _ _ row_return_one, leftAt_cons]
      congr 1
      omega
    rw [first, ih]
    simp only [List.reverse_cons, registerBits_append, registerBits,
      List.append_nil, List.append_assoc, List.cons_append]
    rw [ones_snoc]
    congr 1
    omega

/-- Return from the selected separator across every preceding register. -/
theorem return_file (pre : List Nat) (h : Int) (l Y : List Bool) :
    zipRun machine253
      (zAt returnOnes h ((registerBits pre).reverse ++ l) (false :: Y)) (width pre + 1) =
    leftAt returnZero (h - (width pre : Int)) l
      (registerBits pre ++ false :: Y) := by
  simpa only [reverse_registerBits, width_reverse, List.reverse_reverse] using
    return_file_left pre.reverse h l Y

/-- The four actual transitions that detect zero and restore its unary one. -/
theorem restore_zero_steps (h : Int) (l X : List Bool) :
    zipRun machine253 (zAt seekDec h l (false :: false :: false :: X)) 4 =
      zAt returnOnes h l (false :: true :: false :: X) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ row_seek_zero,
    zipRun_first, step_right _ _ _ _ _ _ _ _ row_probe_zero,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_test_zero, leftAt_cons,
    zipRun_first, step_left _ _ _ _ _ _ _ _ row_restore_zero, leftAt_cons]
  simp only [zipRun]
  congr 1
  omega

/-- An exact symbolic execution, with no bound on prefix lengths or values. -/
theorem zero_box_zip (pre : List Nat) (h : Int) (l X : List Bool) :
    zipRun machine253
      (zAt seekDec h l (registerBits pre ++ false :: false :: false :: X))
      (2 * width pre + 5) =
    leftAt returnZero h l (registerBits pre ++ false :: true :: false :: X) := by
  rw [show 2 * width pre + 5 = width pre + (4 + (width pre + 1)) by omega,
    zipRun_add, forward_file, zipRun_add, restore_zero_steps, return_file]
  congr 1
  omega

private theorem registerBits_blank_end (rest : List Nat) :
    ∃ X, registerBits rest ++ [false] = false :: X := by
  cases rest with
  | nil => exact ⟨[], rfl⟩
  | cons v vs => exact ⟨true :: (List.replicate v true ++ registerBits vs ++ [false]), by
      simp [registerBits]⟩

/-- The register-file form: restore the marked zero and preserve every other
block, including an arbitrary finite spare suffix and the blank exterior. -/
theorem zero_decrement_zip (pre rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machine253
      (zAt seekDec h l (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))
      (2 * width pre + 5) =
    leftAt returnZero h l (registerBits (pre ++ 0 :: rest) ++ [false]) := by
  obtain ⟨X, hX⟩ := registerBits_blank_end rest
  simpa only [registerBits_append, registerBits, List.replicate_zero,
    List.nil_append, List.cons_append, List.append_assoc, hX] using zero_box_zip pre h l X

/-- Actual Core execution for every represented configuration, not a finite
test of register values. The output specifies the entire infinite tape. -/
theorem zero_decrement {c : Config 253} (pre rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt seekDec h l (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))) :
    ZipRep (machine253.runFrom c (2 * width pre + 5))
      (leftAt returnZero h l (registerBits (pre ++ 0 :: rest) ++ [false])) := by
  have hs := zipRun_sound machine253 (2 * width pre + 5) hc
  rw [zero_decrement_zip] at hs
  exact hs

theorem zero_decrement_state {c : Config 253} (pre rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt seekDec h l (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))) :
    (machine253.runFrom c (2 * width pre + 5)).state = some returnZero :=
  (zero_decrement pre rest h l hc).1

theorem zero_decrement_head {c : Config 253} (pre rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt seekDec h l (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))) :
    (machine253.runFrom c (2 * width pre + 5)).head = h - 1 :=
  (zero_decrement pre rest h l hc).2.1

/-- Pointwise equality with the complete output frame, including cells outside
the finite lists. Tape lists themselves need not have a canonical order. -/
theorem zero_decrement_tape {c : Config 253} (pre rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt seekDec h l (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))
    (pos : Int) :
    Tape.read (machine253.runFrom c (2 * width pre + 5)).tape pos =
      frameRead (leftAt returnZero h l (registerBits (pre ++ 0 :: rest) ++ [false])) pos :=
  read_eq_frameRead (zero_decrement pre rest h l hc) pos

#print axioms forward_file
#print axioms return_file
#print axioms zero_decrement_zip
#print axioms zero_decrement
#print axioms zero_decrement_state
#print axioms zero_decrement_head
#print axioms zero_decrement_tape

end SetTheory.BusyBeaver.ZFC.RegisterBoxes253
