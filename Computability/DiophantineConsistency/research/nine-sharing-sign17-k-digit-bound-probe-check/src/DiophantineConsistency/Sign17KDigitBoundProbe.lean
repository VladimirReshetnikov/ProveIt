import DiophantineConsistency.Sign17KRadixStreamCurrent

/-! SOURCE ONLY. Conditional stream digit bounds and selected literal blocks. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KDigitBoundProbe

open CurrentKernel2011

theorem stream_bound (v : Fin 986 → ℕ)
    (h : ∀ i, v i + 1 < radix) (d : ℕ)
    (hd : d ∈ Sign17KRadixStream.digits v) : d < radix := by
  have hr : 2 ≤ radix := by decide +kernel
  simp only [Sign17KRadixStream.digits, Sign17KRadixStream.lowPrefix,
    Sign17KRadixStream.suffix, Sign17KRadixStream.block, List.mem_append,
    List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false,
    ne_eq, Nat.reduceEq, not_false_eq_true, true_and, List.mem_ofFn] at hd
  rcases hd with h0 | h1 | h2 | hb | h3 | h4
  · omega
  · omega
  · omega
  · rcases hb with ⟨i, rfl⟩
    have hi := h i.rev
    split_ifs <;> omega
  · omega
  · omega

theorem first_block_bound (i : Fin 32) :
    Sign17KTileCoefficients00.literal i + 1 < radix := by
  fin_cases i <;> decide +kernel

theorem tail_block_bound (i : Fin 14) :
    Sign17KTileCoefficients15.literal i + 1 < radix := by
  fin_cases i <;> decide +kernel

theorem control_block_bound (i : Fin 44) :
    Sign17KControlBlocks.literal i + 1 < radix := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KDigitBoundProbe
#print axioms DiophantineConsistency.Sign17KDigitBoundProbe.stream_bound
#print axioms DiophantineConsistency.Sign17KDigitBoundProbe.first_block_bound
#print axioms DiophantineConsistency.Sign17KDigitBoundProbe.tail_block_bound
#print axioms DiophantineConsistency.Sign17KDigitBoundProbe.control_block_bound
