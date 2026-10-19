import BusyBeaver.ZFC.Rotation240Boxes

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC
open FiniteZipper ZipperRuns RegisterBoxesPerm252 Rotation240Boxes

#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.carryBits_snoc
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.carry_file
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.return_separator
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.positive_decrement_zip
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.rollback_file
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.zero_decrement_zip
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.carry_end
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.shift_suffix
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.increment_zip
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.positive_decrement_boundary
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.positive_decrement
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.zero_decrement
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.increment
#print axioms SetTheory.BusyBeaver.ZFC.Rotation240Boxes.following_nonempty

-- These names refer to the exact rotation240 state map, never the252 map.
example : Rotation240Boxes.carry = oldStateRotation240 95 := rfl
example : Rotation240Boxes.seek = oldStateRotation240 73 := rfl
example : Rotation240Boxes.returnZero = oldStateRotation240 48 := rfl
example : Rotation240Boxes.rollback = oldStateRotation240 112 := rfl

example (pre : List Nat) (X : List Bool) :
    carryBits pre ++ true :: X = true :: (registerBits pre ++ X) :=
  carryBits_snoc pre X

example (pre : List Nat) (h : Int) (l X : List Bool) :
    zipRun machineRotation240
      (zAt Rotation240Boxes.carry h l (registerBits pre ++ X)) (width pre) =
      zAt Rotation240Boxes.carry (h + (width pre : Int)) ((carryBits pre).reverse ++ l) X :=
  carry_file pre h l X

example (pre : List Nat) (h : Int) (l Y : List Bool) :
    zipRun machineRotation240
      (leftAt Rotation240Boxes.rollback h ((carryBits pre).reverse ++ l) Y) (width pre) =
      leftAt Rotation240Boxes.rollback (h - (width pre : Int)) l (registerBits pre ++ Y) :=
  rollback_file pre h l Y

example (pre : List Nat) (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt Rotation240Boxes.carry h l
        (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))
      (2 * width pre + 4) =
      zAt Rotation240Boxes.returnZero h l (true :: registerBits (pre ++ v :: rest)) :=
  positive_decrement_zip pre v rest h l

example (pre : List Nat) (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt Rotation240Boxes.carry h l
        (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))
      (2 * width pre + 4) =
      leftAt Rotation240Boxes.returnZero (h + 1) (true :: l) (registerBits (pre ++ v :: rest)) :=
  positive_decrement_boundary pre v rest h l

example (pre : List Nat) (next : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt Rotation240Boxes.carry h l
        (registerBits pre ++ false :: false :: registerBits (next :: rest)))
      (2 * width pre + 7) =
      leftAt Rotation240Boxes.rollback h l (registerBits (pre ++ 0 :: next :: rest)) :=
  zero_decrement_zip pre next rest h l

example (pre : List Nat) (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt Rotation240Boxes.seek h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)))
      (2 * width (pre ++ v :: rest) + 7) =
      leftAt Rotation240Boxes.returnZero h l (registerBits ((pre ++ (v + 1) :: rest) ++ [1])) :=
  increment_zip pre v rest h l

example (c : Config 240) (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt Rotation240Boxes.carry h l
      (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))) :
    ZipRep (machineRotation240.runFrom c (2 * width pre + 4))
      (zAt Rotation240Boxes.returnZero h l (true :: registerBits (pre ++ v :: rest))) :=
  positive_decrement pre v rest h l hc

example (c : Config 240) (pre : List Nat) (next : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt Rotation240Boxes.carry h l
      (registerBits pre ++ false :: false :: registerBits (next :: rest)))) :
    ZipRep (machineRotation240.runFrom c (2 * width pre + 7))
      (leftAt Rotation240Boxes.rollback h l (registerBits (pre ++ 0 :: next :: rest))) :=
  zero_decrement pre next rest h l hc

example (c : Config 240) (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt Rotation240Boxes.seek h l
      (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)))) :
    ZipRep (machineRotation240.runFrom c (2 * width (pre ++ v :: rest) + 7))
      (leftAt Rotation240Boxes.returnZero h l (registerBits ((pre ++ (v + 1) :: rest) ++ [1]))) :=
  increment pre v rest h l hc

example (pre rest : List Nat) (v : Nat)
    (hp : pre.length < 9) (hf : 10 ≤ (pre ++ v :: rest).length) : rest ≠ [] :=
  following_nonempty pre rest v hp hf

-- The positive contract includes physical register0 and an empty spare suffix;
-- only the zero contract requires an actual following block.
example (v : Nat) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt Rotation240Boxes.carry h l (false :: false :: List.replicate (v + 1) true)) 4 =
      zAt Rotation240Boxes.returnZero h l (true :: registerBits [v]) := by
  simpa only [registerBits, width, List.nil_append, List.append_nil,
    Nat.mul_zero, Nat.zero_add] using positive_decrement_zip [] v [] h l

-- Every positive-decrement duration is positive, uniformly in all values.
example (pre : List Nat) : 0 < 2 * width pre + 4 := by omega
example (pre : List Nat) : 0 < 2 * width pre + 7 := by omega
example (pre : List Nat) (v : Nat) (rest : List Nat) :
    0 < 2 * width (pre ++ v :: rest) + 7 := by omega
