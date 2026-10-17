import BusyBeaver.ZFC.ArithmeticCommandBlocks254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandAppend254 ArithmeticCommandBlocks254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_pair_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_append_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_consMp
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_consDrop
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_consNip
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_consAx
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.packed_nil
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.packed_encode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_nips
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_discard
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_leaf
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_bundleLeaf
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_genBlock
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandBlocks254.Circuit.eval_mpBlock
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (c : Circuit) (e : Fin 5 → V) : c.graph.val.Evalb e ↔
    e 0 = c.eval (e 1) (e 2) (e 3) (e 4) := (Circuit.defined c).df e
example (c : Circuit) (a b d u : V) : ∃! out, c.graph.val.Evalb ![out,a,b,d,u] := by simp
example (a b c u : V) : Circuit.zero.eval a b c u = 0 := rfl
example (a b c u : V) : Circuit.one.eval a b c u = 1 := rfl
example (a b c u : V) : (Circuit.plus .input0 .input1).eval a b c u = a+b := rfl
example (a b c u : V) : (Circuit.pair .input0 .input1).eval a b c u = cantor a b := rfl
example (a b c u : V) : (Circuit.append .input0 .input1).eval a b c u = appendValue a b := rfl
end Generic
example (a b c u : Nat) : (Circuit.mp .input0).eval a b c u = CommandWord254.encode [.mp a] := by
  simp only [Circuit.mp, Circuit.eval_consMp, Circuit.eval_input0, Circuit.eval_zero, Circuit.packed_nil]
example (a b c u : Nat) : (Circuit.drop .input0).eval a b c u = CommandWord254.encode [.drop a] := by
  simp only [Circuit.drop, Circuit.eval_consDrop, Circuit.eval_input0, Circuit.eval_zero, Circuit.packed_nil]
example (a b c u : Nat) : (Circuit.nip .input0).eval a b c u = CommandWord254.encode [.nip a] := by
  simp only [Circuit.nip, Circuit.eval_consNip, Circuit.eval_input0, Circuit.eval_zero, Circuit.packed_nil]
example (a b c u : Nat) : (Circuit.ax .input0 .input1 .input2 .input3).eval a b c u =
    CommandWord254.encode [.ax a b c u] := by
  simp only [Circuit.ax, Circuit.eval_consAx, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_input3, Circuit.eval_zero, Circuit.packed_nil]
example (k a b c u : Nat) : (Circuit.nips k).eval a b c u = CommandWord254.encode (Enum254.nips k) := Circuit.eval_nips k a b c u
example (a b c u : Nat) : Circuit.discard.eval a b c u = CommandWord254.encode Enum254.discard := Circuit.eval_discard a b c u
example (a b c u : Nat) : Circuit.leaf1.eval a b c u = CommandWord254.encode (Enum254.leaf 1 a b 0 0) := by
  simp only [Circuit.leaf1, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_zero]
example (a b c u : Nat) : Circuit.leaf2.eval a b c u = CommandWord254.encode (Enum254.leaf 2 a b c 0) := by
  simp only [Circuit.leaf2, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_zero]
example (a b c u : Nat) : Circuit.leaf3.eval a b c u = CommandWord254.encode (Enum254.leaf 3 a b c 0) := by
  simp only [Circuit.leaf3, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_zero]
example (a b c u : Nat) : Circuit.leaf4.eval a b c u = CommandWord254.encode (Enum254.leaf 4 a b c 0) := by
  simp only [Circuit.leaf4, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_zero]
example (a b c u : Nat) : Circuit.leaf5.eval a b c u = CommandWord254.encode (Enum254.leaf 5 a b c 0) := by
  simp only [Circuit.leaf5, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_zero]
example (a b c u : Nat) : Circuit.leaf6.eval a b c u = CommandWord254.encode (Enum254.leaf 6 a b 0 0) := by
  simp only [Circuit.leaf6, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_zero]
example (a b c u : Nat) : Circuit.leaf7.eval a b c u = CommandWord254.encode (Enum254.leaf 7 a b c 0) := by
  simp only [Circuit.leaf7, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_zero]
example (a b c u : Nat) : Circuit.leaf8.eval a b c u = CommandWord254.encode (Enum254.leaf 8 a b c u) := by
  simp only [Circuit.leaf8, Circuit.eval_leaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2, Circuit.eval_input3]
example (a b c u : Nat) : (Circuit.bundleLeaf .input0 .input1 .input2).eval a b c u =
    CommandWord254.encode (Enum254.bundleLeaf a b c) := by simp only [Circuit.eval_bundleLeaf, Circuit.eval_input0, Circuit.eval_input1, Circuit.eval_input2]
example (i p : Circuit) (a b c u : Nat) (word : List Enum254.Cmd)
    (h : p.eval a b c u = CommandWord254.encode word) :
    (Circuit.genBlock i p).eval a b c u = CommandWord254.encode (Enum254.genBlock (i.eval a b c u) word) := Circuit.eval_genBlock i p a b c u word h
example (B p q : Circuit) (a b c u : Nat) (minor major : List Enum254.Cmd)
    (hp : p.eval a b c u = CommandWord254.encode minor) (hq : q.eval a b c u = CommandWord254.encode major) :
    (Circuit.mpBlock B p q).eval a b c u = CommandWord254.encode (Enum254.mpBlock (B.eval a b c u) minor major) := Circuit.eval_mpBlock B p q a b c u minor major hp hq

example (c : Enum254.Cmd) : Enum254.pack c 0 + 1 = CommandWord254.encode [c] := Circuit.packed_nil c
