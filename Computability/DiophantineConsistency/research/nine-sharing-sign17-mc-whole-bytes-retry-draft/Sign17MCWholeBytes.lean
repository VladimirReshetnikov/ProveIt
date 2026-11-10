import DiophantineConsistency.Sign17MCComposeBlocks

/-! SOURCE-ONLY: assemble checked blocks into the symbolic MC port. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCWholeBytes
open CurrentMasks2011 Sign17MCRadixRuns Sign17MCComposeBlocks

theorem merge_replicates {α : Type} (a : α) (m n : ℕ) (tail : List α) :
    List.replicate m a ++ (List.replicate n a ++ tail) =
      List.replicate (m + n) a ++ tail := by
  rw [← List.append_assoc, ← List.replicate_add]

theorem runs_eq_blocks : runs = digitBlocks.flatten ++ digitsF := by
  simp only [runs, digitBlocks, digitsA, digitsB, digitsC, digitsD, digitsE, digitsF,
    List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.flatten_replicate_replicate, List.append_nil, List.append_assoc,
    merge_replicates, List.replicate_append_replicate, Nat.reduceAdd, Nat.reduceMul]

noncomputable def mcBytesLE : List ℕ := byteBlocks.flatten ++ bytesF

theorem low_port_bytes : lowPort = Nat.ofDigits 256 mcBytesLE := by
  rw [low_port_runs, runs_eq_blocks]
  exact blocks_value

theorem current_port2_bytes : CurrentWindowCarry2011.ports 2 =
    (Nat.ofDigits 256 mcBytesLE : ℕ) := by
  change (lowPort : ℤ) = (Nat.ofDigits 256 mcBytesLE : ℕ)
  exact_mod_cast low_port_bytes

end DiophantineConsistency.Sign17MCWholeBytes
#print axioms DiophantineConsistency.Sign17MCWholeBytes.runs_eq_blocks
#print axioms DiophantineConsistency.Sign17MCWholeBytes.low_port_bytes
#print axioms DiophantineConsistency.Sign17MCWholeBytes.current_port2_bytes
