import BusyBeaver.ZFC.RegisterMarkPrefix250

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterMarkPrefix250 RegisterBoxesPerm252 FiniteZipper ZipperRuns

#print axioms skip_one_facts
#print axioms skip_next_facts
#print axioms skip_file
#print axioms mark_steps
#print axioms mark_word
#print axioms mark_zip
#print axioms mark
#print axioms mark_with_suffix

example (v : Nat) (rest : List Nat) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt (skip 0) h l (registerBits (v :: rest))) 3 =
    leftAt markFirst h l (false :: false :: (List.replicate v true ++ registerBits rest)) := by
  simpa only [List.length_nil, width, registerBits, List.nil_append, markExit,
    if_pos rfl, if_true, Nat.mul_zero, Nat.zero_add] using
    mark_zip [] v rest (by decide) h l

example (pre : List Nat) (v : Nat) (rest : List Nat) (hp : pre.length < 9)
    (hne : pre ≠ []) (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))
      (2 * width pre + 3) =
    leftAt markReturnZero h l
      (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest)) := by
  simpa only [markExit, if_neg hne] using mark_zip pre v rest hp h l

example {c : Config 250} (pre : List Nat) (v : Nat) (rest : List Nat)
    (hp : pre.length < 9) (h : Int) (l : List Bool)
    (hc : ZipRep c (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest)))) :
    ZipRep (machinePrefix250.runFrom c (2 * width pre + 3))
      (leftAt (markExit pre) h l
        (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest))) :=
  mark pre v rest hp h l hc

example (pre : List Nat) (v : Nat) (rest : List Nat) (hp : pre.length < 9)
    (h : Int) (l : List Bool) :
    zipRun machinePrefix250
      (zAt (skip pre.length) h l (registerBits (pre ++ v :: rest) ++ [false]))
      (2 * width pre + 3) =
    leftAt (markExit pre) h l
      (registerBits pre ++ false :: false :: (List.replicate v true ++ registerBits rest ++ [false])) := by
  simpa only [registerBits_append, registerBits, List.cons_append, List.append_assoc] using
    mark_word pre v hp h l (registerBits rest ++ [false])
