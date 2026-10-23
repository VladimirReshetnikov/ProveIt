import DiophantineConsistency.MaskPopulation

open Jones1982 DiophantineConsistency DiophantineConsistency.MaskPopulation

-- The mask includes a selected position zero and omits interior positions.
example : σ 2 (LowMaskCoding.mask (2 ^ 3) (2 ^ 1) 4 {0, 2}) + 2 * 1 = 4 * 3 := by
  simpa using low_mask_population (k := 1) (t := 3) (n := 4) (by decide) (by decide) {0, 2}
    (by decide : ({0, 2} : Finset ℕ) ⊆ Finset.range 4)

example : σ 2 (highMask (2 ^ 3) {0, 3}) = 2 * (3 - 1) := by
  simpa using high_mask_population (by decide : 1 ≤ 3) {0, 3}
    (by decide : ({0, 3} : Finset ℕ) ⊆ Finset.range 4)

example : σ 2 (packedMask (2 ^ 3) (2 ^ 1) 4 {0, 2} {0, 3}) + 2 * 1 + 2 = (4 + 2) * 3 := by
  simpa using packed_population (by decide : 1 ≤ 3) (by decide : 1 ≤ 3) {0, 2} {0, 3}
    (by decide : ({0, 2} : Finset ℕ) ⊆ Finset.range 4)
    (by decide : ({0, 3} : Finset ℕ) ⊆ Finset.range 4)

#print axioms population_ofDigits
#print axioms low_mask_population
#print axioms high_mask_population
#print axioms packed_population
#print axioms split116_mask_population
#print axioms split116_binomial_iff
