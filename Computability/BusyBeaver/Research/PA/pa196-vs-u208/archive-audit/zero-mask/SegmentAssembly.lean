import SegmentBase
/-! Assemble the bounded row checks for the generated segmented table. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA196ZeroMask
open M6.Source
theorem allFromChunks
    (segment0 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (0+i.val) = true)
    (segment256 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (256+i.val) = true)
    (segment512 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (512+i.val) = true)
    (segment768 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (768+i.val) = true)
    (segment1024 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (1024+i.val) = true)
    (segment1280 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (1280+i.val) = true)
    (segment1536 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (1536+i.val) = true)
    (segment1792 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (1792+i.val) = true)
    (segment2048 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (2048+i.val) = true)
    (segment2304 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (2304+i.val) = true)
    (segment2560 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (2560+i.val) = true)
    (segment2816 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (2816+i.val) = true)
    (segment3072 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (3072+i.val) = true)
    (segment3328 : ∀ i : Fin 256, rowOK segmentedLookup segmentedCertificate (3328+i.val) = true)
    (segment3584 : ∀ i : Fin 228, rowOK segmentedLookup segmentedCertificate (3584+i.val) = true)
    (pc : Nat) : rowOK segmentedLookup segmentedCertificate pc = true := by
  by_cases hp : pc < 3812
  · have hc : pc < 256 ∨ (256 ≤ pc ∧ pc < 512) ∨ (512 ≤ pc ∧ pc < 768) ∨ (768 ≤ pc ∧ pc < 1024) ∨ (1024 ≤ pc ∧ pc < 1280) ∨ (1280 ≤ pc ∧ pc < 1536) ∨ (1536 ≤ pc ∧ pc < 1792) ∨ (1792 ≤ pc ∧ pc < 2048) ∨ (2048 ≤ pc ∧ pc < 2304) ∨ (2304 ≤ pc ∧ pc < 2560) ∨ (2560 ≤ pc ∧ pc < 2816) ∨ (2816 ≤ pc ∧ pc < 3072) ∨ (3072 ≤ pc ∧ pc < 3328) ∨ (3328 ≤ pc ∧ pc < 3584) ∨ (3584 ≤ pc ∧ pc < 3812) := by omega
    rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
    · have ht := segment0 ⟨pc - 0, by omega⟩
      have heq : 0 + (pc - 0) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment256 ⟨pc - 256, by omega⟩
      have heq : 256 + (pc - 256) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment512 ⟨pc - 512, by omega⟩
      have heq : 512 + (pc - 512) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment768 ⟨pc - 768, by omega⟩
      have heq : 768 + (pc - 768) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment1024 ⟨pc - 1024, by omega⟩
      have heq : 1024 + (pc - 1024) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment1280 ⟨pc - 1280, by omega⟩
      have heq : 1280 + (pc - 1280) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment1536 ⟨pc - 1536, by omega⟩
      have heq : 1536 + (pc - 1536) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment1792 ⟨pc - 1792, by omega⟩
      have heq : 1792 + (pc - 1792) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment2048 ⟨pc - 2048, by omega⟩
      have heq : 2048 + (pc - 2048) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment2304 ⟨pc - 2304, by omega⟩
      have heq : 2304 + (pc - 2304) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment2560 ⟨pc - 2560, by omega⟩
      have heq : 2560 + (pc - 2560) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment2816 ⟨pc - 2816, by omega⟩
      have heq : 2816 + (pc - 2816) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment3072 ⟨pc - 3072, by omega⟩
      have heq : 3072 + (pc - 3072) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment3328 ⟨pc - 3328, by omega⟩
      have heq : 3328 + (pc - 3328) = pc := by omega
      simpa only [heq] using ht
    · have ht := segment3584 ⟨pc - 3584, by omega⟩
      have heq : 3584 + (pc - 3584) = pc := by omega
      simpa only [heq] using ht
  · have hn : segmentedLookup pc = none := by simp [segmentedLookup, hp]
    simp [rowOK, hn]
#print axioms allFromChunks
end PA196ZeroMask
