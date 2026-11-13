import MaskEncoding
import MaskSets
import Transfer
set_option autoImplicit false
namespace PA196ZeroMask
open M6.Source

theorem positiveSet_bit (m : Mask) (r : Fin 9) :
    (positiveSet r).testBit (encode m) = m r := by
  have h := (finite_sets r ⟨encode m, encode_bound m⟩).1
  simpa only [encode_testBit] using h

theorem zeroSet_bit (m : Mask) (r : Fin 9) :
    (zeroSet r).testBit (encode m) = !(m r) := by
  have h := (finite_sets r ⟨encode m, encode_bound m⟩).2
  simpa only [encode_testBit] using h

structure TableClosed (lookup : Nat → Option Instruction) (certificate : Nat → Nat) : Prop where
  inc : ∀ pc r target, lookup pc = some (.inc r (some target)) →
    incCheck (certificate pc) (certificate target) (positiveSet r) (zeroSet r) (2^r.val) = true
  dec_zero : ∀ pc r target positive, lookup pc = some (.dec r (some target) positive) →
    maskSub (certificate pc &&& zeroSet r) (certificate target) = true
  dec_positive : ∀ pc r zero target, lookup pc = some (.dec r zero (some target)) →
    maskSub ((certificate pc &&& positiveSet r) |||
      ((certificate pc &&& positiveSet r) >>> (2^r.val))) (certificate target) = true
  jump : ∀ pc target, lookup pc = some (.jump (some target)) →
    maskSub (certificate pc) (certificate target) = true

theorem closed_of_table (sites : Array Site) (lookup : Nat → Option Instruction)
    (certificate : Nat → Nat)
    (binding : ∀ pc, resolveAt sites pc = lookup pc)
    (checks : TableClosed lookup certificate) :
    Closed sites (fun pc m => (certificate pc).testBit (encode m) = true) := by
  constructor
  · intro pc m r target hr hm
    have hrow : lookup pc = some (.inc r (some target)) := by rw [← binding pc]; exact hr
    have hcheck := checks.inc pc r target hrow
    cases hb : m r with
    | false =>
      have hz : (zeroSet r).testBit (encode m) = true := by simp [zeroSet_bit, hb]
      have ht := inc_zero hcheck hm hz
      simpa [encode_set_true, hb] using ht
    | true =>
      have hp : (positiveSet r).testBit (encode m) = true := by simp [positiveSet_bit, hb]
      have ht := inc_positive hcheck hm hp
      simpa [encode_set_true, hb] using ht
  · intro pc m r target positive hr hm hb
    have hrow : lookup pc = some (.dec r (some target) positive) := by rw [← binding pc]; exact hr
    have hcheck := checks.dec_zero pc r target positive hrow
    have hz : (zeroSet r).testBit (encode m) = true := by simp [zeroSet_bit, hb]
    apply maskSub_sound hcheck
    simp [hm, hz]
  · intro pc m r zero target b hr hm hb
    have hrow : lookup pc = some (.dec r zero (some target)) := by rw [← binding pc]; exact hr
    have hcheck := checks.dec_positive pc r zero target hrow
    have hp : (positiveSet r).testBit (encode m) = true := by simp [positiveSet_bit, hb]
    cases b with
    | true =>
      have hsource : ((certificate pc &&& positiveSet r) |||
          ((certificate pc &&& positiveSet r) >>> (2^r.val))).testBit (encode m) = true := by simp [hm, hp]
      have ht := maskSub_sound hcheck hsource
      simpa [encode_set_true, hb] using ht
    | false =>
      have hmpos : (encode m).testBit r = true := by simpa only [encode_testBit] using hb
      have hle : 2^r.val ≤ encode m := Nat.ge_two_pow_of_testBit hmpos
      have heq : 2^r.val + (encode m - 2^r.val) = encode m := by omega
      have hsource : ((certificate pc &&& positiveSet r) |||
          ((certificate pc &&& positiveSet r) >>> (2^r.val))).testBit (encode m - 2^r.val) = true := by
        simp [Nat.testBit_shiftRight, heq, hm, hp]
      have ht := maskSub_sound hcheck hsource
      simpa [encode_set_false, hb] using ht
  · intro pc m target hr hm
    have hrow : lookup pc = some (.jump (some target)) := by rw [← binding pc]; exact hr
    exact maskSub_sound (checks.jump pc target hrow) hm

#print axioms positiveSet_bit
#print axioms zeroSet_bit
#print axioms closed_of_table
end PA196ZeroMask
