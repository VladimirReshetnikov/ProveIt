import BusyBeaver.ZFC.SymbolicRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open SymbolicRouting245

#print axioms SymbolicRouting245.box_head
#print axioms SymbolicRouting245.box_mark
#print axioms SymbolicRouting245.box_increment
#print axioms SymbolicRouting245.box_zero_decrement
#print axioms SymbolicRouting245.box_positive_decrement
#print axioms SymbolicRouting245.box_back
#print axioms SymbolicRouting245.skipTarget_sound
#print axioms SymbolicRouting245.skipTarget_complete
#print axioms SymbolicRouting245.sstep_sound
#print axioms SymbolicRouting245.exec_sound
#print axioms SymbolicRouting245.matches_sound
#print axioms SymbolicRouting245.exec_to_matches
#print axioms SymbolicRouting245.exec_to_halt
#print axioms SymbolicRouting245.verifies_sound
#print axioms SymbolicRouting245.verifiesHalt_sound

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
      ⟨some (RegisterMarkRouting245.skip r.val), false, l, [.box (.plain .unchanged)]⟩
      ⟨some (markExit r), true, l, [.box (.marked r)]⟩ false := box_mark br r l

example (br : Branch) (r : Reg) (l : List Segment) :
    StepSound br
      ⟨some Routing245Boxes.seek, false, l, [.box (.marked r)]⟩
      ⟨some Routing245Boxes.returnZero, true, l, [.box (.plain (.increment r))]⟩ false :=
  box_increment br r l

example (r : Reg) (l : List Segment) :
    StepSound (some (r, true))
      ⟨some Routing245Boxes.carry, false, l, [.box (.marked r)]⟩
      ⟨some Routing245Boxes.rollback, true, l, [.box (.plain .unchanged)]⟩ false :=
  box_zero_decrement r l

example (r : Reg) (l : List Segment) :
    StepSound (some (r, false))
      ⟨some Routing245Boxes.carry, false, l, [.box (.marked r)]⟩
      ⟨some Routing245Boxes.returnZero, true, .bit true :: l,
        [.box (.plain (.decrement r))]⟩ false := box_positive_decrement r l

example (q : Fin 245) (r : Reg) (hs : skipTarget q = some r) :
    q = RegisterMarkRouting245.skip r.val := skipTarget_sound q r hs

example (br : Branch) (s t : SConfig) (m : Bool)
    (hs : sstep br s = some (t, m)) : StepSound br s t m := sstep_sound br s t m hs

example (fuel : Nat) (br : Branch) (target : SConfig → Bool)
    (s t : SConfig) (moved : Bool) (he : exec fuel br target s moved = some t) :
    target t = true ∧ StepSound br s t (!moved) := exec_sound fuel br target s t moved he

example (s t : SConfig) (hm : isMatch s t = true)
    (n : Nat) (vs : List Nat) (c : Config 245)
    (hc : Represents n vs s c) : Represents n vs t c := matches_sound s t hm n vs c hc

example (fuel : Nat) (br : Branch) (s wanted : SConfig)
    (he : verifies fuel br s wanted = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 245)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ Represents n vs wanted (machineRouting245.runFrom c k) :=
  verifies_sound fuel br s wanted he n vs hv c hc

example (fuel : Nat) (br : Branch) (s : SConfig)
    (he : verifiesHalt fuel br s = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) (c : Config 245)
    (hc : Represents n vs s c) :
    ∃ k : Nat, 0 < k ∧ (machineRouting245.runFrom c k).state = none :=
  verifiesHalt_sound fuel br s he n vs hv c hc

example (br : Branch) (q : Fin 245) (next : Option (Fin 245))
    (x : Box) (l : List Segment)
    (ht : machineRouting245.transition q false = ⟨false, .left, next⟩) :
    StepSound br ⟨some q, false, l, [.box x]⟩ ⟨next, true, l, [.box x]⟩ true :=
  box_back br q next x l ht

example (r : Reg) : skipTarget (RegisterMarkRouting245.skip r.val) = some r :=
  skipTarget_complete r
