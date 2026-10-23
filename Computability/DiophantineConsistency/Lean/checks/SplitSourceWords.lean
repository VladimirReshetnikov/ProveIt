import DiophantineConsistency.SplitSourceWords

open DiophantineConsistency.SplitSourceWords Polynomial

private noncomputable def fixture : Parameters where
  w := fun i => i.val + 86
  q := fun i => i.val
  D0 := monomial 1719 (-1)
  D1 := monomial 2027 (-1)
  D2 := monomial 1929 1

private theorem fixture_valid : Valid fixture 0 := by
  constructor
  · intro i j h
    apply Fin.ext
    change i.val + 86 = j.val + 86 at h
    omega
  · intro i
    change i.val + 86 ≤ 116
    omega
  · exact ⟨⟨30, by decide⟩, rfl⟩
  · intro i j h
    exact Fin.ext h
  · intro i
    change i.val ≤ 2129
    omega
  · constructor
    · exact natDegree_monomial_le (-1 : ℤ)
    · exact natDegree_monomial_le (-1 : ℤ)
    · exact natDegree_monomial_le (1 : ℤ)
    · intro i; simp only [fixture, coeff_monomial]; split_ifs <;> norm_num
    · intro i; simp only [fixture, coeff_monomial]; split_ifs <;> norm_num
    · intro i; simp only [fixture, coeff_monomial]; split_ifs <;> norm_num
    · simp [fixture]

-- Negative lower layers, zero or arbitrarily large code: no cap is used.
example (g : ℕ) : 0 < highInt fixture 0 1 g := highInt_pos fixture_valid (by decide) g
example (g : ℕ) : 0 < word fixture 0 1 g := word_pos fixture_valid (by decide) g

-- The separate weak cap is sufficient for the range used by the carry test.
example (g : ℕ)
    (hg : g < 4 * (DiophantineConsistency.SplitNineRatio.base 0 1) ^ 116) :
    word fixture 0 1 g < DiophantineConsistency.SplitNineRatio.blockLength 0 1 := by
  exact (weak_cap_bounds fixture_valid (by decide) (by simpa only [mul_one] using hg)).2

#print axioms sum_positions
#print axioms highInt_eq
#print axioms scale
#print axioms highInt_pos
#print axioms word_pos
#print axioms word_cast
#print axioms mask_eq_population
#print axioms mask_cast
#print axioms weak_cap_bounds
#print axioms rank_cast
