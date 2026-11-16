import Abstraction
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA196ZeroMask

def decode (n : Nat) : Mask := fun r => n.testBit r

theorem decode_encode (m : Mask) : decode (encode m) = m := by
  funext r
  exact encode_testBit m r

theorem finite_updates : ∀ (r : Fin 9) (n : Fin 512),
    encode (setMask (decode n) r true) = (if n.val.testBit r then n.val else n.val + 2^r.val) ∧
    encode (setMask (decode n) r false) = (if n.val.testBit r then n.val - 2^r.val else n.val) := by decide
theorem encode_set_true (m : Mask) (r : Fin 9) :
    encode (setMask m r true) = (if m r then encode m else encode m + 2^r.val) := by
  have h := (finite_updates r ⟨encode m, encode_bound m⟩).1
  simpa only [decode_encode, encode_testBit] using h

theorem encode_set_false (m : Mask) (r : Fin 9) :
    encode (setMask m r false) = (if m r then encode m - 2^r.val else encode m) := by
  have h := (finite_updates r ⟨encode m, encode_bound m⟩).2
  simpa only [decode_encode, encode_testBit] using h
#print axioms finite_updates
#print axioms encode_set_true
#print axioms encode_set_false
end PA196ZeroMask
