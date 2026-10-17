import BusyBeaver.ZFC.ArithmeticProofWord254
import BusyBeaver.ZFC.Code254ProofCompiler

/-!
Exact standard finite raw-tree quotation adapter.

The theorem covers every finite RawProof tree, including invalid proofs. The
word generator itself is unconditional. The result identifies ordinary-Nat
quotation with the exact existing structural compiler. Validity-conditional
internal execution and PA consistency transport remain separate obligations.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofWordQuote254

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open Code254 Code254Proof Code254ProofCompiler
open ArithmeticCantor ArithmeticProofWordRow254 ArithmeticProofWord254
open ArithmeticCommandBlocks254

attribute [local irreducible] P CommandWord254.encode Enum254.nips Enum254.discard
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

/-- Remove exactly the proof node's positive marker, not an extra command marker. -/
theorem rawWord_node (tag payload : Nat) (ht : tag < 12) :
    rawWord (V := Nat) (node tag payload) = rowValue tag payload
      (if tag = 2 then rawWord (second payload)
       else rawWord (first (second payload))) (rawWord (second (second payload))) := by
  have hm : (12 * payload + tag) % 12 = tag := by omega
  have hd : (12 * payload + tag) / 12 = payload := by omega
  have hs := rawWord_succ (V := Nat) (12 * payload + tag)
  rw [← ArithmeticHistory254.numeral_twelve_eq_twelve (V := Nat),
    ← numeral_two_eq_two (M := Nat)] at hs
  simp only [Nat.numeral_eq, HMod.hMod, HDiv.hDiv] at hs
  rw [ArithmeticHistory254.foundation_rem_nat, ArithmeticHistory254.foundation_div_nat] at hs
  simpa only [node, hm, hd] using hs

/-- Exact standard quotation agreement, with no validity hypothesis. -/
theorem rawWord_quote (p : RawProof) :
    rawWord (V := Nat) p.quote = CommandWord254.encode (compile p) := by
  induction p with
  | truth =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, ↓reduceIte]
      exact Circuit.eval_discard 0 0 0 0
  | mp b p q ihp ihq =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [show (1 : Nat) ≠ 2 by decide, if_false, first_nat, second_nat, unP_P]
      simp only [rowValue, ↓reduceIte, first_nat, unP_P]
      exact Circuit.eval_mpBlock .input0 .input1 .input2 b (rawWord p.quote) (rawWord q.quote) 0
        (compile p) (compile q) ihp ihq
  | gen a p ih =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [first_nat, second_nat, unP_P]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_genBlock .input0 .input1 a (rawWord p.quote) 0 0 (compile p) ih
  | r1 a b =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 1 .input0 .input1 .zero .zero a b 0 0
  | r2 a b c =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 2 .input0 .input1 .input2 .zero a b c 0
  | r3 a b c =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 3 .input0 .input1 .input2 .zero a b c 0
  | r4 a b c =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 4 .input0 .input1 .input2 .zero a b c 0
  | r5 a b c =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 5 .input0 .input1 .input2 .zero a b c 0
  | r6 a b =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 6 .input0 .input1 .zero .zero a b 0 0
  | r7 a b c =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 7 .input0 .input1 .input2 .zero a b c 0
  | r8 a b c u =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_leaf 8 .input0 .input1 .input2 .input3 a b c u
  | bundle a b c =>
      rw [RawProof.quote, rawWord_node _ _ (by decide)]
      simp only [rowValue, first_nat, second_nat, unP_P]
      exact Circuit.eval_bundleLeaf .input0 .input1 .input2 a b c 0

end SetTheory.BusyBeaver.ZFC.ArithmeticProofWordQuote254
