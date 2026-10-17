import BusyBeaver.ZFC.ArithmeticProofWordQuote254

open SetTheory.BusyBeaver.ZFC
open Code254 Code254Proof Code254ProofCompiler
open ArithmeticCantor ArithmeticProofWordRow254 ArithmeticProofWord254
open ArithmeticProofWordQuote254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordQuote254.rawWord_node
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordQuote254.rawWord_quote

example (tag payload : Nat) (ht : tag < 12) :
    rawWord (V := Nat) (node tag payload) = rowValue tag payload
      (if tag = 2 then rawWord (second payload)
       else rawWord (first (second payload))) (rawWord (second (second payload))) :=
  rawWord_node tag payload ht

example (p : RawProof) : rawWord (V := Nat) p.quote = CommandWord254.encode (compile p) :=
  rawWord_quote p

example : rawWord (V := Nat) RawProof.truth.quote = CommandWord254.encode Enum254.discard :=
  rawWord_quote .truth

example (b : Nat) (p q : RawProof) : rawWord (V := Nat) (.mp b p q : RawProof).quote =
    CommandWord254.encode (Enum254.mpBlock b (compile p) (compile q)) :=
  rawWord_quote (.mp b p q)

example (a : Nat) (p : RawProof) : rawWord (V := Nat) (.gen a p : RawProof).quote =
    CommandWord254.encode (Enum254.genBlock a (compile p)) := rawWord_quote (.gen a p)

example (a b : Nat) : rawWord (V := Nat) (.r1 a b : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 1 a b 0 0) := rawWord_quote (.r1 a b)
example (a b c : Nat) : rawWord (V := Nat) (.r2 a b c : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 2 a b c 0) := rawWord_quote (.r2 a b c)
example (a b c : Nat) : rawWord (V := Nat) (.r3 a b c : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 3 a b c 0) := rawWord_quote (.r3 a b c)
example (a b c : Nat) : rawWord (V := Nat) (.r4 a b c : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 4 a b c 0) := rawWord_quote (.r4 a b c)
example (a b c : Nat) : rawWord (V := Nat) (.r5 a b c : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 5 a b c 0) := rawWord_quote (.r5 a b c)
example (a b : Nat) : rawWord (V := Nat) (.r6 a b : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 6 a b 0 0) := rawWord_quote (.r6 a b)
example (a b c : Nat) : rawWord (V := Nat) (.r7 a b c : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 7 a b c 0) := rawWord_quote (.r7 a b c)
example (a b c u : Nat) : rawWord (V := Nat) (.r8 a b c u : RawProof).quote =
    CommandWord254.encode (Enum254.leaf 8 a b c u) := rawWord_quote (.r8 a b c u)
example (a b c : Nat) : rawWord (V := Nat) (.bundle a b c : RawProof).quote =
    CommandWord254.encode (Enum254.bundleLeaf a b c) := rawWord_quote (.bundle a b c)

-- The raw constructor equality is deliberately unconditional, even at these invalid trees.
example : rawWord (V := Nat) (.bundle 0 0 0 : RawProof).quote =
    CommandWord254.encode (compile (.bundle 0 0 0)) := rawWord_quote (.bundle 0 0 0)
example : rawWord (V := Nat) (.mp 1 .truth .truth : RawProof).quote =
    CommandWord254.encode (compile (.mp 1 .truth .truth)) := rawWord_quote (.mp 1 .truth .truth)
example (a b : Nat) : rawWord (V := Nat) (.gen a (.gen b .truth) : RawProof).quote =
    CommandWord254.encode (compile (.gen a (.gen b .truth))) :=
  rawWord_quote (.gen a (.gen b .truth))
example : rawWord (V := Nat) 0 = 0 := rawWord_zero
