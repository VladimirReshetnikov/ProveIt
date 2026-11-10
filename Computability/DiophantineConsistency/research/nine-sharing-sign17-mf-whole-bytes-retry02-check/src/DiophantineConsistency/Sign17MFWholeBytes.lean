import DiophantineConsistency.Sign17MFComposeBlocks

/-! SOURCE-ONLY: assemble checked MF blocks into the symbolic source port. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MFWholeBytes
open CurrentMasks2011 Sign17MFRadixDigits Sign17MFComposeBlocks

theorem merge_replicates {α : Type} (a : α) (m n : ℕ) (tail : List α) :
    List.replicate m a ++ (List.replicate n a ++ tail) =
      List.replicate (m + n) a ++ tail := by
  rw [← List.append_assoc, ← List.replicate_add]

theorem merge_cons {α : Type} (a : α) (m : ℕ) (tail : List α) :
    List.replicate m a ++ (a :: tail) = List.replicate (m + 1) a ++ tail := by
  simpa only [List.replicate_one, List.singleton_append] using merge_replicates a m 1 tail

theorem digits_eq_blocks : mfDigits = digitBlocks.flatten ++ digitsJ := by
  simp only [mfDigits, tailDigits, digitBlocks, digitsA, digitsB, digitsC, digitsD,
    digitsE, digitsF, digitsG, digitsH, digitsI, digitsJ, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.flatten_replicate_replicate,
    List.append_nil, List.nil_append, List.cons_append, List.append_assoc, merge_replicates, List.replicate_append_replicate,
    List.replicate_one, List.singleton_append, merge_cons, Nat.reduceAdd, Nat.reduceMul]

noncomputable def mfBytesLE : List ℕ := byteBlocks.flatten ++ bytesJ

theorem mf_port_bytes : highPort + beta = Nat.ofDigits 256 mfBytesLE := by
  rw [← mf_digits_value, digits_eq_blocks]
  exact blocks_value

theorem current_port3_bytes : CurrentWindowCarry2011.ports 3 =
    (Nat.ofDigits 256 mfBytesLE : ℕ) := by
  change ((highPort + beta : ℕ) : ℤ) = (Nat.ofDigits 256 mfBytesLE : ℕ)
  exact_mod_cast mf_port_bytes

end DiophantineConsistency.Sign17MFWholeBytes
#print axioms DiophantineConsistency.Sign17MFWholeBytes.digits_eq_blocks
#print axioms DiophantineConsistency.Sign17MFWholeBytes.mf_port_bytes
#print axioms DiophantineConsistency.Sign17MFWholeBytes.current_port3_bytes
