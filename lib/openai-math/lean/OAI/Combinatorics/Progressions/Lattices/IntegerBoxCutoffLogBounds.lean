import OAI.Combinatorics.Progressions.Lattices.AffineMeshRetention

namespace OAI

section

namespace Erdos3

noncomputable def integerBoxGcdCutoff (d : ℕ) (C epsilon : ℝ) : ℕ :=
  ⌈2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon⌉₊ + 1

noncomputable def integerBoxNearRatio (d : ℕ) (epsilon : ℝ) : ℝ :=
  replacementAccuracy (2 * (3 : ℝ) ^ d) epsilon

noncomputable def integerBoxPairScale (d : ℕ) (C epsilon : ℝ) : ℝ :=
  max (integerBoxGcdCutoff d C epsilon : ℝ) (1 / integerBoxNearRatio d epsilon)

noncomputable def integerBoxRetainedGap (d D : ℕ) (c epsilon : ℝ) : ℝ :=
  (D : ℝ) * integerBoxNearRatio d epsilon * c

theorem integerBoxGcdCutoff_spec (d : ℕ) {C epsilon : ℝ}
    (heps : 0 < epsilon) :
    0 < integerBoxGcdCutoff d C epsilon ∧
      (2 : ℝ) ^ (d - 1) * (1 + C) / integerBoxGcdCutoff d C epsilon ≤ epsilon / 2 := by
  have hp : 0 < integerBoxGcdCutoff d C epsilon := by
    unfold integerBoxGcdCutoff
    omega
  refine ⟨hp, ?_⟩
  have hpr : (0 : ℝ) < integerBoxGcdCutoff d C epsilon := by exact_mod_cast hp
  have hceil : 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon ≤
      (integerBoxGcdCutoff d C epsilon : ℝ) := by
    unfold integerBoxGcdCutoff
    push_cast
    linarith [Nat.le_ceil (2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon)]
  have hh := (div_le_iff₀ heps).mp hceil
  apply (div_le_iff₀ hpr).mpr
  nlinarith

theorem integerBoxNearRatio_spec (d : ℕ) {epsilon : ℝ} (heps : 0 < epsilon) :
    0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
      (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon / 2 := by
  have h := replacementAccuracy_spec (by positivity : 0 ≤ 2 * (3 : ℝ) ^ d) heps
  change 0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
    2 * (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon at h
  exact ⟨h.1, h.2.1, by linarith [h.2.2]⟩

theorem integerBoxBadPairBudget_of_cutoffs (d R : ℕ) {C epsilon M : ℝ}
    (hd : 2 ≤ d) (hC : 0 ≤ C) (heps : 0 < epsilon)
    (hscale : integerBoxPairScale d C epsilon ≤ M) (hR : (R : ℝ) ≤ C * M) :
    integerBoxBadPairBudget d (integerBoxGcdCutoff d C epsilon) R
      ⌊integerBoxNearRatio d epsilon * M⌋₊ M ≤ epsilon := by
  have hB := integerBoxGcdCutoff_spec d (C := C) heps
  have hnu := integerBoxNearRatio_spec d heps
  have hBM : (integerBoxGcdCutoff d C epsilon : ℝ) ≤ M := (le_max_left _ _).trans hscale
  have hM : 0 < M := (by exact_mod_cast hB.1 : (0 : ℝ) < integerBoxGcdCutoff d C epsilon).trans_le hBM
  have hinv : 1 / M ≤ integerBoxNearRatio d epsilon := by
    have h := (le_max_right (integerBoxGcdCutoff d C epsilon : ℝ)
      (1 / integerBoxNearRatio d epsilon)).trans hscale
    have hh := (div_le_iff₀ hnu.1).mp h
    apply (div_le_iff₀ hM).mpr
    nlinarith
  have h := integerBoxBadPairBudget_le_linear d (integerBoxGcdCutoff d C epsilon) R
    ⌊integerBoxNearRatio d epsilon * M⌋₊ hd hB.1 hBM hC hR
    (Nat.floor_le (mul_nonneg hnu.1.le hM.le)) hinv hnu.2.1
  linarith [hB.2, hnu.2.2]

theorem integerBoxRetainedGap_spec (d D : ℕ) {c epsilon L M : ℝ}
    (hD : 0 < D) (hc : 0 < c) (heps : 0 < epsilon) (hside : c * L ≤ M) :
    0 < integerBoxRetainedGap d D c epsilon ∧
      integerBoxRetainedGap d D c epsilon * L ≤
        (D : ℝ) * (⌊integerBoxNearRatio d epsilon * M⌋₊ + 1 : ℕ) := by
  have hnu := (integerBoxNearRatio_spec d heps).1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · unfold integerBoxRetainedGap
    positivity
  · unfold integerBoxRetainedGap
    push_cast
    calc
      _ = (D : ℝ) * (integerBoxNearRatio d epsilon * (c * L)) := by ring
      _ ≤ (D : ℝ) * (integerBoxNearRatio d epsilon * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hside hnu.le) hDr.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le hDr.le

end Erdos3

end

section

namespace Erdos3

theorem integerBoxGcdCutoff_le_exp (d : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxGcdCutoff d C epsilon : ℝ) ≤ Real.exp (3 * P + 6) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hsum := one_add_le_exp_succ hP hC
  have hx : 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon ≤ Real.exp (3 * P + 3) := by
    calc
      _ = 2 * (2 : ℝ) ^ (d - 1) * (1 + C) * epsilon⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ Real.exp 2 * Real.exp P * Real.exp (P + 1) * Real.exp P := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon)).le
  have hbase : 1 ≤ Real.exp (3 * P + 3) := Real.one_le_exp_iff.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    (integerBoxGcdCutoff d C epsilon : ℝ) ≤ Real.exp (3 * P + 3) + 2 := by
      unfold integerBoxGcdCutoff
      push_cast
      linarith
    _ ≤ 3 * Real.exp (3 * P + 3) := by linarith
    _ ≤ Real.exp 3 * Real.exp (3 * P + 3) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem integerBoxNearRatio_inverse_le_exp (d : ℕ) {epsilon P : ℝ}
    (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : 2 * (3 : ℝ) ^ d ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxNearRatio d epsilon)⁻¹ ≤ Real.exp (2 * P + 2) :=
  replacementAccuracy_inverse_le_exp (by positivity) heps0 hP hpow heps

theorem integerBoxPairScale_le_exp (d : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow2 : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hpow3 : 2 * (3 : ℝ) ^ d ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    integerBoxPairScale d C epsilon ≤ Real.exp (3 * P + 6) := by
  apply max_le (integerBoxGcdCutoff_le_exp d hC0 heps0 hP hpow2 hC heps)
  rw [one_div]
  exact (integerBoxNearRatio_inverse_le_exp d heps0 hP hpow3 heps).trans
    (Real.exp_le_exp.mpr (by linarith))

theorem integerBoxRetainedGap_inverse_le_exp (d D : ℕ) {c epsilon P : ℝ}
    (hD : 0 < D) (hc0 : 0 < c) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : 2 * (3 : ℝ) ^ d ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (integerBoxRetainedGap d D c epsilon)⁻¹ ≤ Real.exp (3 * P + 2) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDinv : (D : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hD1
  have hnu0 := (integerBoxNearRatio_spec d heps0).1
  have hnu := integerBoxNearRatio_inverse_le_exp d heps0 hP hpow heps
  calc
    _ = (D : ℝ)⁻¹ * (integerBoxNearRatio d epsilon)⁻¹ * c⁻¹ := by
      simp only [integerBoxRetainedGap, mul_inv_rev]
      ring
    _ ≤ 1 * Real.exp (2 * P + 2) * Real.exp P := by gcongr
    _ = _ := by rw [one_mul, ← Real.exp_add]; congr 1; ring

theorem integerBoxGcdModulus_le_exp (d D : ℕ) {C epsilon P : ℝ}
    (hC0 : 0 ≤ C) (heps0 : 0 < epsilon) (hP : 0 ≤ P)
    (hpow : (2 : ℝ) ^ (d - 1) ≤ Real.exp P)
    (hD : (D : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    ((D * integerBoxGcdCutoff d C epsilon : ℕ) : ℝ) ≤ Real.exp (4 * P + 6) := by
  rw [Nat.cast_mul]
  calc
    _ ≤ Real.exp P * Real.exp (3 * P + 6) :=
      mul_le_mul hD (integerBoxGcdCutoff_le_exp d hC0 heps0 hP hpow hC heps)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
