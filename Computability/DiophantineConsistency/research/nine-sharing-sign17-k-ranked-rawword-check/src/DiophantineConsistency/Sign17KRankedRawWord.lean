import DiophantineConsistency.Sign17KRankedTileSum

/-! SOURCE-ONLY: split actual rawWord into ranked tile and all control terms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KRankedRawWord
open CurrentKernel2011 WangTiles942
open scoped BigOperators

def controls (r : ℕ) : ℕ :=
    (∑ j : Fin 8, 2 * 2 ^ (10 + j.val) * r ^ (1005 - (978 + j.val))) +
    (∑ j : Fin 9, 2 * 2 ^ (18 + j.val) * r ^ (1005 - (960 + j.val))) +
    (∑ j : Fin 8, 2 * 2 ^ (27 + j.val) * r ^ (1005 - (969 + j.val))) +
    (∑ j : Fin 9, 2 * 2 ^ (35 + j.val) * r ^ (1005 - (942 + j.val)))

theorem rawWord_ranked (r : ℕ) :
    rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020 +
      (∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val)) +
      controls r := by
  unfold rawWord controls
  simp only [Fintype.sum_sum_type, coefficient, exponent, position, weight]
  rw [Fin.sum_univ_three]
  simp only [one_mul]
  rw [Sign17KRankedTileSum.ranked_tile_sum]
  ring

theorem K_ranked : K = radix ^ 18 + radix ^ 1004 + radix ^ 2020 +
      (∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * radix ^ (1005 - i.val)) +
      controls radix := by
  exact rawWord_ranked radix

end DiophantineConsistency.Sign17KRankedRawWord
#print axioms DiophantineConsistency.Sign17KRankedRawWord.rawWord_ranked
#print axioms DiophantineConsistency.Sign17KRankedRawWord.K_ranked
