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
  change d ∈ Sign17KRadixStream.lowPrefix ++
    (Sign17KRadixStream.block v ++ Sign17KRadixStream.suffix) at hd
  rcases List.mem_append.mp hd with hp | hrest
  · change d ∈ List.replicate 18 0 ++ [1, 0] at hp
    simp only [List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with ⟨_, h0⟩ | h1 | h0 <;> omega
  · rcases List.mem_append.mp hrest with hb | hs
    · change d ∈ List.ofFn (fun i : Fin 986 =>
        v i.rev + if i = ⟨984, by decide⟩ then 1 else 0) at hb
      rcases List.mem_ofFn.mp hb with ⟨i, hi⟩
      have hv := h i.rev
      split_ifs at hi <;> omega
    · change d ∈ List.replicate 1014 0 ++ [1] at hs
      simp only [List.mem_append, List.mem_replicate, List.mem_cons,
        List.not_mem_nil, or_false] at hs
      rcases hs with ⟨_, h0⟩ | h1 <;> omega

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
