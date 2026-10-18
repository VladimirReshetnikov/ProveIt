import BusyBeaver.ZFC.SymbolicPrefix250

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open SymbolicPrefix250

#print axioms SymbolicPrefix250.box_head
#print axioms SymbolicPrefix250.box_mark
#print axioms SymbolicPrefix250.box_increment
#print axioms SymbolicPrefix250.box_zero_decrement
#print axioms SymbolicPrefix250.box_positive_decrement
#print axioms SymbolicPrefix250.box_back
#print axioms SymbolicPrefix250.skipTarget_sound
#print axioms SymbolicPrefix250.sstep_sound
#print axioms SymbolicPrefix250.exec_sound
#print axioms SymbolicPrefix250.matches_sound
#print axioms SymbolicPrefix250.exec_to_matches
#print axioms SymbolicPrefix250.exec_to_halt
#print axioms SymbolicPrefix250.verifies_sound
#print axioms SymbolicPrefix250.verifiesHalt_sound

-- The two changed effects encode every spare explicitly.
example (r : Reg) (vs : List Nat) :
    boxBits (.plain (.increment r)) vs =
      RegisterBoxesPerm252.registerBits (incr r.val vs ++ [1]) := rfl

example (r : Reg) (vs : List Nat) :
    boxBits (.plain (.decrement r)) vs =
      RegisterBoxesPerm252.registerBits (decr r.val vs) := rfl

example (br : Branch) (vs : List Nat) (hv : Valid br vs) : 10 ≤ vs.length := hv.1

example (br : Branch) (r : Reg) (l : List Segment) :
    StepSound br
      ⟨some (RegisterMarkPrefix250.skip r.val), false, l, [.box (.plain .unchanged)]⟩
      ⟨some (markExit r), true, l, [.box (.marked r)]⟩ false := box_mark br r l

example (br : Branch) (r : Reg) (l : List Segment) :
    StepSound br
      ⟨some Prefix250Boxes.seek, false, l, [.box (.marked r)]⟩
      ⟨some Prefix250Boxes.returnZero, true, l, [.box (.plain (.increment r))]⟩ false :=
  box_increment br r l

example (r : Reg) (l : List Segment) :
    StepSound (some (r, true))
      ⟨some Prefix250Boxes.carry, false, l, [.box (.marked r)]⟩
      ⟨some Prefix250Boxes.rollback, true, l, [.box (.plain .unchanged)]⟩ false :=
  box_zero_decrement r l

example (r : Reg) (l : List Segment) :
    StepSound (some (r, false))
      ⟨some Prefix250Boxes.carry, false, l, [.box (.marked r)]⟩
      ⟨some Prefix250Boxes.returnZero, true, .bit true :: l,
        [.box (.plain (.decrement r))]⟩ false := box_positive_decrement r l

example (q : Fin 250) (r : Reg) (hs : skipTarget q = some r) :
    q = RegisterMarkPrefix250.skip r.val := skipTarget_sound q r hs

example (br : Branch) (s t : SConfig) (m : Bool)
    (hs : sstep br s = some (t, m)) : StepSound br s t m := sstep_sound br s t m hs

example (fuel : Nat) (br : Branch) (target : SConfig → Bool)
    (s t : SConfig) (moved : Bool) (he : exec fuel br target s moved = some t) :
    target t = true ∧ StepSound br s t (!moved) := exec_sound fuel br target s t moved he

example (s t : SConfig) (hm : isMatch s t = true)
    (n : Nat) (vs : List Nat) (c : Config 250)
    (hc : Represents n vs s c) : Represents n vs t c := matches_sound s t hm n vs c hc

example (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : verifies fuel br s wanted = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 250)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ Represents n vs wanted (machinePrefix250.runFrom c k) :=
  verifies_sound fuel br s wanted he n vs hv c hc

example (fuel : Nat) (br : Branch) (s : SConfig)
    (he : verifiesHalt fuel br s = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 250)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ (machinePrefix250.runFrom c k).state = none :=
  verifiesHalt_sound fuel br s he n vs hv c hc

example (br : Branch) (q : Fin 250) (next : Option (Fin 250))
    (x : Box) (l : List Segment)
    (ht : machinePrefix250.transition q false = ⟨false, .left, next⟩) :
    StepSound br ⟨some q, false, l, [.box x]⟩ ⟨next, true, l, [.box x]⟩ true :=
  box_back br q next x l ht
