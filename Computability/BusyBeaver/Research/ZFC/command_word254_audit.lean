import BusyBeaver.ZFC.CommandWord254
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open Code254 Enum254
open CommandWord254
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.encode_cons
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.encode_decode
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.decode_encode
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.encode_injective
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.encode_eq_zero
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.tail_le
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.tail_pack
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.replaceRest_pack
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.replaceRest_self
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.append_zero
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.append_succ
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.append_encode
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.append_decode
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.append_right_zero
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.append_assoc
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.raw_zero_is_nonempty
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.word_zero_is_empty
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.tail_formula
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.replaceRest_formula
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.tail_replaceRest
#print axioms SetTheory.BusyBeaver.ZFC.CommandWord254.replaceRest_replaceRest
example (c : Cmd) (cs : List Cmd) : encode (c::cs) = encL c cs + 1 := encode_cons c cs
example (n : Nat) : encode (decode n) = n := encode_decode n
example (cs : List Cmd) : decode (encode cs) = cs := decode_encode cs
example (xs ys : List Cmd) (h : encode xs = encode ys) : xs = ys := encode_injective h
example (cs : List Cmd) : encode cs = 0 ↔ cs = [] := encode_eq_zero cs
example (z : Nat) : tail z ≤ z := tail_le z
example (c : Cmd) (r : Nat) : tail (pack c r) = r := tail_pack c r
example (c : Cmd) (old r : Nat) : replaceRest (pack c old) r = pack c r := replaceRest_pack c old r
example (z : Nat) : replaceRest z (tail z) = z := replaceRest_self z
example (r : Nat) : append 0 r = r := append_zero r
example (z r : Nat) : append (z+1) r = replaceRest z (append (tail z) r)+1 := append_succ z r
example (xs ys : List Cmd) : append (encode xs) (encode ys) = encode (xs++ys) := append_encode xs ys
example (l r : Nat) : append l r = encode (decode l ++ decode r) := append_decode l r
example (l : Nat) : append l 0 = l := append_right_zero l
example (a b c : Nat) : append (append a b) c = append a (append b c) := append_assoc a b c
example : encode [.mp 0] = 1 := raw_zero_is_nonempty
example : decode 0 = [] := word_zero_is_empty
example : decode 1 = [.mp 0] := by
  simpa only [raw_zero_is_nonempty] using decode_encode [.mp 0]
example : encode [] = 0 := rfl
example (z : Nat) : tail z = tailFormula z := tail_formula z
example (z r : Nat) : replaceRest z r = replaceRestFormula z r := replaceRest_formula z r
example (z r : Nat) : tail (replaceRest z r) = r := tail_replaceRest z r
example (z old r : Nat) : replaceRest (replaceRest z old) r = replaceRest z r := replaceRest_replaceRest z old r
example : append 1 1 = encode [.mp 0,.mp 0] := by
  simpa only [raw_zero_is_nonempty, List.cons_append, List.nil_append] using append_encode [.mp 0] [.mp 0]
example (c : Cmd) : encode [c] > 0 := by simp [encode]
