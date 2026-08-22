import ExponentialIdentities.TwoBaseIntegerExponent

/-!
# A fixed integral-matrix reformulation of Alaoglu--Erdős

The split integral matrix with eigenvalues two and three has an explicit real-power matrix.
This module formalizes that all four entries are integral exactly when `2 ^ t` and `3 ^ t`
are integral, and hence packages the conjecture as a statement about its integral real times.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The explicit spectral-calculus formula for the real `t`-th power of
`!![0, -6; 1, 5]`, whose eigenvalues are two and three. -/
def splitTwoThreeRealPowerMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j ↦
    if i = 0 then
      if j = 0 then 3 * (2 : ℝ) ^ t - 2 * (3 : ℝ) ^ t
      else 6 * (2 : ℝ) ^ t - 6 * (3 : ℝ) ^ t
    else
      if j = 0 then (3 : ℝ) ^ t - (2 : ℝ) ^ t
      else 3 * (3 : ℝ) ^ t - 2 * (2 : ℝ) ^ t

@[simp] theorem splitTwoThreeRealPowerMatrix_zero_zero (t : ℝ) :
    splitTwoThreeRealPowerMatrix t 0 0 =
      3 * (2 : ℝ) ^ t - 2 * (3 : ℝ) ^ t := by simp [splitTwoThreeRealPowerMatrix]

@[simp] theorem splitTwoThreeRealPowerMatrix_zero_one (t : ℝ) :
    splitTwoThreeRealPowerMatrix t 0 1 =
      6 * (2 : ℝ) ^ t - 6 * (3 : ℝ) ^ t := by simp [splitTwoThreeRealPowerMatrix]

@[simp] theorem splitTwoThreeRealPowerMatrix_one_zero (t : ℝ) :
    splitTwoThreeRealPowerMatrix t 1 0 =
      (3 : ℝ) ^ t - (2 : ℝ) ^ t := by simp [splitTwoThreeRealPowerMatrix]

@[simp] theorem splitTwoThreeRealPowerMatrix_one_one (t : ℝ) :
    splitTwoThreeRealPowerMatrix t 1 1 =
      3 * (3 : ℝ) ^ t - 2 * (2 : ℝ) ^ t := by simp [splitTwoThreeRealPowerMatrix]

/-- Every entry of a real matrix is the cast of an integer. -/
def HasIntegralEntries {m n : Type*} (B : Matrix m n ℝ) : Prop :=
  ∀ i j, B i j ∈ Set.range ((↑) : ℤ → ℝ)

/-- The explicit real-power matrix is integral exactly when its two spectral values are
integers. -/
theorem splitTwoThreeRealPowerMatrix_hasIntegralEntries_iff (t : ℝ) :
    HasIntegralEntries (splitTwoThreeRealPowerMatrix t) ↔
      (2 : ℝ) ^ t ∈ Set.range ((↑) : ℤ → ℝ) ∧
      (3 : ℝ) ^ t ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h 1 0
    obtain ⟨d, hd⟩ := h 0 0
    refine ⟨⟨d + 2 * c, ?_⟩, ⟨d + 3 * c, ?_⟩⟩
    · simp only [splitTwoThreeRealPowerMatrix_one_zero,
        splitTwoThreeRealPowerMatrix_zero_zero] at hc hd
      norm_num only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      rw [hc, hd]
      ring
    · simp only [splitTwoThreeRealPowerMatrix_one_zero,
        splitTwoThreeRealPowerMatrix_zero_zero] at hc hd
      norm_num only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      rw [hc, hd]
      ring
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ i j
    fin_cases i <;> fin_cases j
    · refine ⟨3 * u - 2 * v, ?_⟩
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      rw [hu, hv]
      simp [splitTwoThreeRealPowerMatrix]
    · refine ⟨6 * u - 6 * v, ?_⟩
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      rw [hu, hv]
      simp [splitTwoThreeRealPowerMatrix]
    · refine ⟨v - u, ?_⟩
      simp only [Int.cast_sub]
      rw [hu, hv]
      simp [splitTwoThreeRealPowerMatrix]
    · refine ⟨3 * v - 2 * u, ?_⟩
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      rw [hu, hv]
      simp [splitTwoThreeRealPowerMatrix]

/-- Exact integral-matrix reformulation of the Alaoglu--Erdős conjecture. -/
theorem alaogluErdosConjecture_iff_splitTwoThreeRealPowerMatrix :
    AlaogluErdosConjecture ↔
      ∀ {t : ℝ}, HasIntegralEntries (splitTwoThreeRealPowerMatrix t) →
        t ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro h t ht
    have hp := (splitTwoThreeRealPowerMatrix_hasIntegralEntries_iff t).mp ht
    exact h hp.1 hp.2
  · intro h t h2 h3
    exact h ((splitTwoThreeRealPowerMatrix_hasIntegralEntries_iff t).mpr ⟨h2, h3⟩)

end

end LeanProofs.TwoBaseIntegerExponent
