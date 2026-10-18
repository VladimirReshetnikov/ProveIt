import BusyBeaver.ZFC.Prefix250Boxes

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC
open FiniteZipper ZipperRuns RegisterBoxesPerm252 Prefix250Boxes

#print axioms Prefix250Boxes.carryBits_snoc
#print axioms Prefix250Boxes.carry_file
#print axioms Prefix250Boxes.return_separator
#print axioms Prefix250Boxes.positive_decrement_zip
#print axioms Prefix250Boxes.rollback_file
#print axioms Prefix250Boxes.zero_decrement_zip
#print axioms Prefix250Boxes.carry_end
#print axioms Prefix250Boxes.shift_suffix
#print axioms Prefix250Boxes.increment_zip
#print axioms Prefix250Boxes.positive_decrement_boundary
#print axioms Prefix250Boxes.positive_decrement
#print axioms Prefix250Boxes.zero_decrement
#print axioms Prefix250Boxes.increment
#print axioms Prefix250Boxes.following_nonempty

-- These names refer to the exact final250 state map, never the252 map.
example : Prefix250Boxes.carry = oldStatePrefix250 95 := rfl
example : Prefix250Boxes.seek = oldStatePrefix250 73 := rfl
example : Prefix250Boxes.returnZero = oldStatePrefix250 48 := rfl
example : Prefix250Boxes.rollback = oldStatePrefix250 112 := rfl

example (pre : List Nat) (X : List Bool) :
    carryBits pre ++ true :: X = true :: (registerBits pre ++ X) :=
  carryBits_snoc pre X

example (pre : List Nat) (h : Int) (l X : List Bool) :
    zipRun machinePrefix250
      (zAt Prefix250Boxes.carry h l (registerBits pre ++ X)) (width pre) =
      zAt Prefix250Boxes.carry (h + (width pre : Int)) ((carryBits pre).reverse ++ l) X :=
  carry_file pre h l X

example (pre : List Nat) (h : Int) (l Y : List Bool) :
    zipRun machinePrefix250
      (leftAt Prefix250Boxes.rollback h ((carryBits pre).reverse ++ l) Y) (width pre) =
      leftAt Prefix250Boxes.rollback (h - (width pre : Int)) l (registerBits pre ++ Y) :=
  rollback_file pre h l Y

example (pre : List Nat) (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt Prefix250Boxes.carry h l
        (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))
      (2 * width pre + 4) =
      zAt Prefix250Boxes.returnZero h l (true :: registerBits (pre ++ v :: rest)) :=
  positive_decrement_zip pre v rest h l

example (pre : List Nat) (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt Prefix250Boxes.carry h l
        (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))
      (2 * width pre + 4) =
      leftAt Prefix250Boxes.returnZero (h + 1) (true :: l) (registerBits (pre ++ v :: rest)) :=
  positive_decrement_boundary pre v rest h l

example (pre : List Nat) (next : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt Prefix250Boxes.carry h l
        (registerBits pre ++ false :: false :: registerBits (next :: rest)))
      (2 * width pre + 7) =
      leftAt Prefix250Boxes.rollback h l (registerBits (pre ++ 0 :: next :: rest)) :=
  zero_decrement_zip pre next rest h l

example (pre : List Nat) (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt Prefix250Boxes.seek h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)))
      (2 * width (pre ++ v :: rest) + 7) =
      leftAt Prefix250Boxes.returnZero h l (registerBits ((pre ++ (v + 1) :: rest) ++ [1])) :=
  increment_zip pre v rest h l

example (c : Config 250) (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt Prefix250Boxes.carry h l
      (registerBits pre ++ false :: false :: (List.replicate (v + 1) true ++ registerBits rest)))) :
    ZipRep (machinePrefix250.runFrom c (2 * width pre + 4))
      (zAt Prefix250Boxes.returnZero h l (true :: registerBits (pre ++ v :: rest))) :=
  positive_decrement pre v rest h l hc

example (c : Config 250) (pre : List Nat) (next : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt Prefix250Boxes.carry h l
      (registerBits pre ++ false :: false :: registerBits (next :: rest)))) :
    ZipRep (machinePrefix250.runFrom c (2 * width pre + 7))
      (leftAt Prefix250Boxes.rollback h l (registerBits (pre ++ 0 :: next :: rest))) :=
  zero_decrement pre next rest h l hc

example (c : Config 250) (pre : List Nat) (v : Nat) (rest : List Nat)
    (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt Prefix250Boxes.seek h l
      (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)))) :
    ZipRep (machinePrefix250.runFrom c (2 * width (pre ++ v :: rest) + 7))
      (leftAt Prefix250Boxes.returnZero h l (registerBits ((pre ++ (v + 1) :: rest) ++ [1]))) :=
  increment pre v rest h l hc

example (pre rest : List Nat) (v : Nat)
    (hp : pre.length < 9) (hf : 10 ≤ (pre ++ v :: rest).length) : rest ≠ [] :=
  following_nonempty pre rest v hp hf

-- The positive contract includes physical register0 and an empty spare suffix;
-- only the zero contract requires an actual following block.
example (v : Nat) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt Prefix250Boxes.carry h l (false :: false :: List.replicate (v + 1) true)) 4 =
      zAt Prefix250Boxes.returnZero h l (true :: registerBits [v]) := by
  simpa only [registerBits, width, List.nil_append, List.append_nil,
    Nat.mul_zero, Nat.zero_add] using positive_decrement_zip [] v [] h l

-- Every positive-decrement duration is positive, uniformly in all values.
example (pre : List Nat) : 0 < 2 * width pre + 4 := by omega
example (pre : List Nat) : 0 < 2 * width pre + 7 := by omega
example (pre : List Nat) (v : Nat) (rest : List Nat) :
    0 < 2 * width (pre ++ v :: rest) + 7 := by omega
