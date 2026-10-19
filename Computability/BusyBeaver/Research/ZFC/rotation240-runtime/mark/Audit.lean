import BusyBeaver.ZFC.RegisterMarkRotation240

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterMarkRotation240 RegisterBoxesPerm252 FiniteZipper ZipperRuns

#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.skip_one_facts
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.skip_next_facts
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.skip_file
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.mark_steps
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.mark_word
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.mark_zip
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.mark
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.mark_with_suffix
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.row_skip_target
#print axioms SetTheory.BusyBeaver.ZFC.RegisterMarkRotation240.row_erase_one

example (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt (skip 0) h l (registerBits (v :: rest))) 3 =
    leftAt markFirst h l (false :: false :: (List.replicate v true ++ registerBits rest)) := by
  simpa only [List.length_nil, width, registerBits, List.nil_append, markExit,
    if_pos rfl, if_true, Nat.mul_zero, Nat.zero_add] using
    mark_zip [] v rest (by decide) h l

example (pre : List Nat) (v : Nat) (rest : List Nat) (hp : pre.length < 9)
    (hne : pre ≠ []) (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))
      (2 * width pre + 3) =
    leftAt markReturnZero h l
      (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)) := by
  simpa only [markExit, if_neg hne] using mark_zip pre v rest hp h l

example {c : Config 240} (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))) :
    ZipRep (machineRotation240.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest))) :=
  mark pre v rest hp h l hc

example (pre : List Nat) (v : Nat) (rest : List Nat) (hp : pre.length < 9)
    (h : Int) (l : List Bool) :
    zipRun machineRotation240
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest) ++ [false]))
      (2 * width pre + 3) =
    leftAt (markExit pre) h l
      (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest ++ [false])) := by
  simpa only [registerBits_append, registerBits, List.cons_append, List.append_assoc] using
    mark_word pre v hp h l (registerBits rest ++ [false])

-- The changed selector entry is the retained old20, never deleted old0.
example : RegisterMarkRotation240.restoreZero = oldStateRotation240 20 := rfl

example : machineRotation240.transition (oldStateRotation240 20) true =
    ⟨false, .left, some markFirst⟩ := row_erase_one
