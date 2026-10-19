import BusyBeaver.ZFC.Rotation240Pulse
import BusyBeaver.ZFC.RegisterMarkPerm252

/-!
Fresh exact240 port of Rotation244Boxes.
The checked predecessor proof bodies are retained under machine/state/module
changes and the exact nine selector literals. Arbitrary registers, complete
tapes and positive clocks remain explicit. Original Mira-Cult, Jeff Ketchersid,
Andrew James Wade and ProveIt attribution is retained.
This generated source is uncompiled; concrete decoder coverage, blank startup
and the final external consistency endpoint require separate actual proofs.
-/
namespace SetTheory.BusyBeaver.ZFC.Rotation240Boxes

open FiniteZipper ZipperRuns RegisterBoxesPerm252

abbrev carry : Fin 240 := oldStateRotation240 95
abbrev carryProbe : Fin 240 := oldStateRotation240 109
abbrev test : Fin 240 := oldStateRotation240 75
abbrev seek : Fin 240 := oldStateRotation240 73
abbrev seekProbe : Fin 240 := oldStateRotation240 83
abbrev returnOnes : Fin 240 := oldStateRotation240 63
abbrev returnZero : Fin 240 := oldStateRotation240 48
abbrev rollback : Fin 240 := oldStateRotation240 112
abbrev rollbackProbe : Fin 240 := oldStateRotation240 131

/-- An ordinary block 01^(v+1) after the forward carry has crossed it. -/
def carryBits : List Nat → List Bool
  | [] => []
  | v :: vs => true :: false :: (List.replicate v true ++ carryBits vs)

/-- The same crossed blocks in nearest-first order on the left half-tape. -/
def carryLeft : List Nat → List Bool
  | [] => []
  | v :: vs => List.replicate v true ++ false :: true :: carryLeft vs

private theorem ones_snoc (v : Nat) (l : List Bool) :
    List.replicate v true ++ true :: l = true :: (List.replicate v true ++ l) := by
  calc
    _ = (List.replicate v true ++ [true]) ++ l := (List.append_assoc _ _ _).symm
    _ = _ := by rw [← List.replicate_succ', List.replicate_succ]; rfl

theorem carryBits_append (a b : List Nat) :
    carryBits (a ++ b) = carryBits a ++ carryBits b := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [carryBits, ih]

theorem carryLeft_append (a b : List Nat) :
    carryLeft (a ++ b) = carryLeft a ++ carryLeft b := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [carryLeft, ih, List.append_assoc]

theorem reverse_carryBits (vs : List Nat) :
    (carryBits vs).reverse = carryLeft vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [carryBits, List.reverse_append, ih, carryLeft_append, carryLeft,
      List.append_assoc]

/-- The last carried one turns the crossed prefix into a one-cell right shift. -/
theorem carryBits_snoc (pre : List Nat) (X : List Bool) :
    carryBits pre ++ true :: X = true :: (registerBits pre ++ X) := by
  induction pre with
  | nil => rfl
  | cons v pre ih =>
    simp only [carryBits, registerBits, List.cons_append, List.append_assoc]
    rw [ih, ones_snoc]

private theorem reverse_carry_snoc (pre : List Nat) (l : List Bool) :
    true :: ((carryBits pre).reverse ++ l) =
      (registerBits pre).reverse ++ true :: l := by
  have hr := congrArg List.reverse (carryBits_snoc pre [])
  simp only [List.append_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append] at hr
  calc
    _ = (true :: (carryBits pre).reverse) ++ l := rfl
    _ = ((registerBits pre).reverse ++ [true]) ++ l := congrArg (fun t => t ++ l) hr
    _ = _ := by simp only [List.append_assoc, List.singleton_append]

/-- Forward carry crosses a separator, replacing01 by10. -/
theorem carry_separator (h : Int) (l X : List Bool) :
    zipRun machineRotation240 (zAt carry h l (false :: true :: X)) 2 =
      zAt carry (h + 2) (false :: true :: l) X := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ rowRotation240_old95_false,
    zipRun_first, step_right _ _ _ _ _ _ _ _ rowRotation240_old109_true]
  simp only [zipRun]
  congr 1
  omega

theorem carry_block (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machineRotation240
      (zAt carry h l (false :: true :: (List.replicate v true ++ X))) (v + 2) =
      zAt carry (h + ((v + 2 : Nat) : Int))
        (List.replicate v true ++ false :: true :: l) X := by
  rw [show v + 2 = 2 + v by omega, zipRun_add, carry_separator,
    scan_right _ _ _ rowRotation240_old95_true]
  congr 1
  omega

/-- This induction is over all prefix lengths and all unary block values. -/
theorem carry_file (pre : List Nat) (h : Int) (l X : List Bool) :
    zipRun machineRotation240 (zAt carry h l (registerBits pre ++ X)) (width pre) =
      zAt carry (h + (width pre : Int)) ((carryBits pre).reverse ++ l) X := by
  induction pre generalizing h l with
  | nil => simp [registerBits, carryBits, width, zipRun]
  | cons v pre ih =>
    simp only [width, registerBits, List.cons_append, List.append_assoc]
    rw [zipRun_add, carry_block, ih]
    simp only [carryBits, List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.singleton_append]
    congr 1
    omega

/-- Two forward steps arrive at the test cell after the marked00. -/
theorem carry_mark (h : Int) (l X : List Bool) :
    zipRun machineRotation240 (zAt carry h l (false :: false :: X)) 2 =
      zAt test (h + 2) (false :: true :: l) X := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ rowRotation240_old95_false,
    zipRun_first, step_right _ _ _ _ _ _ _ _ rowRotation240_old109_false]
  simp only [zipRun]
  congr 1
  omega

/-- The existing return scanner instantiated on three literal244 rows. -/
theorem return_separator (pre : List Nat) (h : Int) (l Y : List Bool) :
    zipRun machineRotation240
      (zAt returnOnes h ((registerBits pre).reverse ++ l) (false :: Y))
      (width pre + 1) =
      leftAt returnZero (h - (width pre : Int)) l (registerBits pre ++ false :: Y) := by
  simpa only [reverse_registerBits, width_reverse, List.reverse_reverse] using
    RegisterMarkPerm252.return_separator_left machineRotation240 returnOnes returnZero
      rowRotation240_old63_true rowRotation240_old63_false rowRotation240_old48_true
      pre.reverse h l Y

/-- A positive selected value v+1 is decreased to v. The boundary moves right one cell;
the final head is at the old origin, which now contains the added left one. -/
theorem positive_decrement_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt carry h l
        (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))
      (2 * width pre + 4) =
      zAt returnZero h l (true :: registerBits (pre ++ v :: rest)) := by
  rw [show 2 * width pre + 4 = width pre + (2 + ((width pre + 1) + 1)) by omega,
    zipRun_add, carry_file, zipRun_add, carry_mark]
  rw [reverse_carry_snoc]
  simp only [List.replicate_succ, List.cons_append]
  rw [zipRun_first, step_left _ _ _ _ _ _ _ _ rowRotation240_old75_true,
    leftAt_cons, return_separator, leftAt_cons]
  simp only [registerBits_append, registerBits]
  congr 1
  omega

/-- The reverse carry changes a crossed 10 pair back to 01. -/
theorem rollback_pair (h : Int) (l Y : List Bool) :
    zipRun machineRotation240 (leftAt rollback h (false :: true :: l) Y) 2 =
      leftAt rollback (h - 2) l (false :: true :: Y) := by
  rw [leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old112_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old131_true]
  simp only [zipRun]
  congr 1
  omega

/-- Restore every crossed block, starting with the nearest block. -/
theorem rollback_left (rp : List Nat) (h : Int) (l Y : List Bool) :
    zipRun machineRotation240 (leftAt rollback h (carryLeft rp ++ l) Y) (width rp) =
      leftAt rollback (h - (width rp : Int)) l (registerBits rp.reverse ++ Y) := by
  induction rp generalizing h Y with
  | nil => simp [width, carryLeft, registerBits, zipRun]
  | cons v rp ih =>
    simp only [width, carryLeft, List.append_assoc, List.cons_append]
    rw [show v + 2 + width rp = v + (2 + width rp) by omega,
      zipRun_add, scan_left _ _ _ rowRotation240_old112_true,
      zipRun_add, rollback_pair, ih]
    simp only [List.reverse_cons, registerBits_append, registerBits,
      List.append_nil, List.append_assoc, List.cons_append]
    congr 1
    omega

theorem rollback_file (pre : List Nat) (h : Int) (l Y : List Bool) :
    zipRun machineRotation240
      (leftAt rollback h ((carryBits pre).reverse ++ l) Y) (width pre) =
      leftAt rollback (h - (width pre : Int)) l (registerBits pre ++ Y) := by
  simpa only [reverse_carryBits, width_reverse, List.reverse_reverse] using
    rollback_left pre.reverse h l Y

/-- On a marked zero followed by an ordinary block, restore the selected 01
and prepare the backwards restoration of the preceding crossed prefix. -/
theorem zero_restore (h : Int) (l X : List Bool) :
    zipRun machineRotation240
      (zAt test h (false :: true :: l) (false :: true :: X)) 5 =
      leftAt rollback (h - 2) l (false :: true :: false :: true :: X) := by
  rw [show 5 = 3 + 2 by decide, zipRun_add, Rotation240Pulse.pulse_zero_one,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old112_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old131_true]
  simp only [zipRun]
  congr 1
  omega

/-- A zero selected register is restored, with output state112 rather than
old 3. The explicit first following block is essential for the zero test. -/
theorem zero_decrement_zip (pre : List Nat) (next : Nat) (rest : List Nat)
    (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt carry h l (registerBits pre ++ false :: false :: registerBits (next :: rest)))
      (2 * width pre + 7) =
      leftAt rollback h l (registerBits (pre ++ 0 :: next :: rest)) := by
  rw [show 2 * width pre + 7 = width pre + (2 + (5 + width pre)) by omega,
    zipRun_add, carry_file, zipRun_add, carry_mark]
  simp only [registerBits]
  rw [zipRun_add, zero_restore, rollback_file]
  simp only [registerBits_append, registerBits, List.replicate_zero,
    List.nil_append]
  congr 1
  omega

/-- The increment seeker passes an ordinary block unchanged. -/
theorem seek_block (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machineRotation240
      (zAt seek h l (false :: true :: (List.replicate v true ++ X))) (v + 2) =
      zAt seek (h + ((v + 2 : Nat) : Int))
        (List.replicate v true ++ true :: false :: l) X := by
  rw [show v + 2 = (v + 1) + 1 by omega, zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRotation240_old73_false, zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRotation240_old83_true,
    scan_right _ _ _ rowRotation240_old73_true]
  congr 1
  omega

theorem seek_file (pre : List Nat) (h : Int) (l X : List Bool) :
    zipRun machineRotation240 (zAt seek h l (registerBits pre ++ X)) (width pre) =
      zAt seek (h + (width pre : Int)) ((registerBits pre).reverse ++ l) X := by
  induction pre generalizing h l with
  | nil => simp [registerBits, width, zipRun]
  | cons v pre ih =>
    simp only [width, registerBits, List.cons_append, List.append_assoc]
    rw [zipRun_add, seek_block, ih]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.singleton_append]
    congr 1
    omega

theorem restore_mark (v : Nat) (h : Int) (l X : List Bool) :
    zipRun machineRotation240
      (zAt seek h l (false :: false :: (List.replicate v true ++ X))) 2 =
      zAt carry (h + 2) (true :: false :: l) (List.replicate v true ++ X) := by
  rw [zipRun_first, step_right _ _ _ _ _ _ _ _ rowRotation240_old73_false,
    zipRun_first, step_right _ _ _ _ _ _ _ _ rowRotation240_old83_false]
  simp only [zipRun]
  congr 1
  omega

private theorem step_right_blank (q q' : Fin 240) (written : Bool)
    (h : Int) (l : List Bool)
    (ht : machineRotation240.transition q false = ⟨written, .right, some q'⟩) :
    zipStep machineRotation240 (zAt q h l []) =
      zAt q' (h + 1) (written :: l) [] := by
  simp [zipStep, zAt, ht, zipWrite, zipRight]

private theorem step_left_blank (q q' : Fin 240) (written : Bool)
    (h : Int) (l : List Bool)
    (ht : machineRotation240.transition q false = ⟨written, .left, some q'⟩) :
    zipStep machineRotation240 (zAt q h l []) = leftAt q' h l [written] := by
  simp [zipStep, zAt, leftAt, ht, zipWrite, zipLeft]

/-- The same zero/zero pulse at the finite representation's blank exterior.
Both previously implicit cells become explicit because they are written. -/
private theorem pulse_blank (h : Int) (l : List Bool) :
    zipRun machineRotation240 (zAt test h l []) 3 =
      leftAt rollbackProbe h l [true, true] := by
  rw [zipRun_first, step_right_blank _ _ _ _ _ rowRotation240_old75_false,
    zipRun_first, step_left_blank _ _ _ _ _ rowRotation240_old255_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old255_true]
  simp only [zipRun]
  congr 1
  omega

/-- Reaching the file's blank end appends 011 and turns left. -/
theorem carry_end (h : Int) (l : List Bool) :
    zipRun machineRotation240 (zAt carry h l []) 6 =
      leftAt returnZero (h + 1) (true :: l) [false, true, true] := by
  rw [zipRun_first, step_right_blank _ _ _ _ _ rowRotation240_old95_false,
    zipRun_first, step_right_blank _ _ _ _ _ rowRotation240_old109_false,
    show 4 = 3 + 1 by decide, zipRun_add, pulse_blank, leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old131_false]
  simp only [zipRun]
  congr 1
  omega

/-- Carry through every following register and spare. Only the zero exterior
is special; all existing suffix values are arbitrary natural numbers. -/
theorem shift_suffix (rest : List Nat) (a : Nat) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt carry h l (List.replicate a true ++ registerBits rest))
      (a + width rest + 6) =
      leftAt returnZero (h + ((a + width rest + 1 : Nat) : Int))
        ((List.replicate (a + 1) true ++ registerBits rest).reverse ++ l)
        [false, true, true] := by
  induction rest generalizing a h l with
  | nil =>
    simp only [width, registerBits, Nat.add_zero]
    rw [zipRun_add _ _ a 6, scan_right _ _ _ rowRotation240_old95_true, carry_end]
    rw [List.append_nil, List.reverse_replicate, List.replicate_succ]
    congr 1
    omega
  | cons v rest ih =>
    simp only [width, registerBits]
    rw [show a + (v + 2 + width rest) + 6 = a + (2 + (v + width rest + 6)) by omega,
      zipRun_add, scan_right _ _ _ rowRotation240_old95_true,
      zipRun_add, carry_separator, ih]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.singleton_append, List.append_assoc, List.replicate_succ]
    simp only [ones_snoc, List.cons_append, List.nil_append]
    congr 1
    omega

/-- The complete increment excursion. Exactly one value-one spare is appended;
all prior suffix registers and all exterior cells are retained. -/
theorem increment_zip (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt seek h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)))
      (2 * width (pre ++ v :: rest) + 7) =
      leftAt returnZero h l (registerBits ((pre ++ (v + 1) :: rest) ++ [1])) := by
  have hne : pre ++ (v + 1) :: rest ≠ [] := by simp
  have firstCount : 2 * width (pre ++ v :: rest) + 7 =
      width pre + (2 + ((v + width rest + 6) + width (pre ++ (v + 1) :: rest))) := by
    simp only [width_append, width]
    omega
  rw [firstCount, zipRun_add, seek_file, zipRun_add]
  simp only [List.append_assoc]
  rw [restore_mark, zipRun_add, shift_suffix]
  have frame :
      (List.replicate (v + 1) true ++ registerBits rest).reverse ++
        true :: false :: ((registerBits pre).reverse ++ l) =
      (registerBits (pre ++ (v + 1) :: rest)).reverse ++ l := by
    simp only [registerBits_append, registerBits, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append]
  rw [frame, RegisterMarkPerm252.return_end machineRotation240 returnOnes returnZero
    rowRotation240_old63_true rowRotation240_old63_false rowRotation240_old48_true
    _ hne returnZero rowRotation240_old48_true]
  simp only [registerBits_append, registerBits, List.replicate_succ,
    List.replicate_zero, List.append_nil, List.append_assoc]
  congr 1
  simp only [width_append, width]
  omega

/-- The same positive endpoint in boundary notation: the file origin moves
right by one and the arbitrary old left context gains exactly one one-cell. -/
theorem positive_decrement_boundary (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt carry h l
        (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))
      (2 * width pre + 4) =
      leftAt returnZero (h + 1) (true :: l) (registerBits (pre ++ v :: rest)) := by
  rw [positive_decrement_zip, leftAt_cons]
  congr 1
  omega

/-- Whole-tape Core contract for positive decrement, with exact duration. -/
theorem positive_decrement {c : Config 240} (pre : List Nat) (v : Nat)
    (rest : List Nat) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt carry h l
      (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))) :
    ZipRep (machineRotation240.runFrom c (2 * width pre + 4))
      (zAt returnZero h l (true :: registerBits (pre ++ v :: rest))) := by
  have hs := zipRun_sound machineRotation240 (2 * width pre + 4) hc
  rw [positive_decrement_zip] at hs
  exact hs

/-- Whole-tape Core contract for zero decrement. The following block can have
any value; its existence is the strengthened runtime invariant's premise. -/
theorem zero_decrement {c : Config 240} (pre : List Nat) (next : Nat)
    (rest : List Nat) (h : Int) (l : List Bool)
    (hc : ZipRep c
      (zAt carry h l (registerBits pre ++ false :: false :: registerBits (next :: rest)))) :
    ZipRep (machineRotation240.runFrom c (2 * width pre + 7))
      (leftAt rollback h l (registerBits (pre ++ 0 :: next :: rest))) := by
  have hs := zipRun_sound machineRotation240 (2 * width pre + 7) hc
  rw [zero_decrement_zip] at hs
  exact hs

/-- Whole-tape Core contract for increment and its new spare block. -/
theorem increment {c : Config 240} (pre : List Nat) (v : Nat)
    (rest : List Nat) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt seek h l
      (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)))) :
    ZipRep (machineRotation240.runFrom c (2 * width (pre ++ v :: rest) + 7))
      (leftAt returnZero h l (registerBits ((pre ++ (v + 1) :: rest) ++ [1]))) := by
  have hs := zipRun_sound machineRotation240 (2 * width (pre ++ v :: rest) + 7) hc
  rw [increment_zip] at hs
  exact hs

/-- A selected index below 9 in a file with at least 10 blocks has a following
block. No bound is placed on its value or on the length of the suffix. -/
theorem following_nonempty (pre rest : List Nat) (v : Nat)
    (hp : pre.length < 9) (hf : 10 ≤ (pre ++ v :: rest).length) : rest ≠ [] := by
  intro he
  subst rest
  simp only [List.length_append, List.length_cons, List.length_nil] at hf
  omega

end SetTheory.BusyBeaver.ZFC.Rotation240Boxes
