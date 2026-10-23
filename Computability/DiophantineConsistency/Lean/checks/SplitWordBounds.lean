import DiophantineConsistency.SplitWordBounds

open DiophantineConsistency.SplitWordBounds Polynomial

private noncomputable def p0 : ℤ[X] := monomial 1719 (-1)
private noncomputable def p1 : ℤ[X] := monomial 2027 (-1)
private noncomputable def p2 : ℤ[X] := monomial 1929 1

private theorem testKernel : KernelBounds p0 p1 p2 1 := by
  constructor
  · exact natDegree_monomial_le (-1 : ℤ)
  · exact natDegree_monomial_le (-1 : ℤ)
  · exact natDegree_monomial_le (1 : ℤ)
  · intro i; simp only [p0, coeff_monomial]; split_ifs <;> norm_num
  · intro i; simp only [p1, coeff_monomial]; split_ifs <;> norm_num
  · intro i; simp only [p2, coeff_monomial]; split_ifs <;> norm_num
  · simp [p2]

-- Both lower layers can be negative. Positivity still holds for every
-- nonnegative g, with no upper code cap or digit-decoding assumption.
example (g : ℤ) (hg : 0 ≤ g) :
    0 < sourceValue p0 p1 p2 4096 ((4096 : ℤ) ^ 116 + g) := by
  have hu : (4096 : ℤ) ^ 116 ≤ 4096 ^ 116 + g := by omega
  exact (source_pos testKernel (by decide) (b := 1) (by decide) (by norm_num) hu).2

-- The explicit degree gaps used by the positivity proof are unchanged.
example : 1929 + 116 - 2027 = 18 := by decide
example : 1929 + 2 * 116 - 1719 = 442 := by decide
example : 117 + 2162 = 2279 := by decide

#print axioms scale_bounds
#print axioms doubled_eval_gt_top
#print axioms scalar_pow_lt
#print axioms negative_layers_lt
#print axioms source_pos
#print axioms abs_eval_scaled_lt
#print axioms source_upper_scaled
#print axioms source_lt_one_sixtyfourth
#print axioms powerSum_lt_two_top
#print axioms top_le_powerSum
#print axioms source_pos_of_word
#print axioms lowMask_bounds
#print axioms unconditional_word_bounds
#print axioms targets_bounds
#print axioms weak_cap_packing
