import OAI.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def externalNetMesh (L : ℝ≥0) (ε : ℝ) : ℝ := ε / (3 * (L + 1))

theorem externalNetMesh_pos (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) : 0 < externalNetMesh L ε := by
  unfold externalNetMesh
  positivity

theorem externalNetMesh_error (L M : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) :
    ε / 3 + M * externalNetMesh M ε + L * externalNetMesh L ε ≤ ε := by
  have hterm (K : ℝ≥0) : K * externalNetMesh K ε ≤ ε / 3 := by
    unfold externalNetMesh
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (K + 1))]
    nlinarith [K.coe_nonneg]
  linarith [hterm M, hterm L]

theorem externalNetMesh_inverse_bound (L : ℝ≥0) {ε p : ℝ}
    (hε : 0 < ε) (hp : 0 ≤ p) (hL : (L : ℝ) ≤ Real.exp p) (hinv : 1 / ε ≤ Real.exp p) :
    1 / externalNetMesh L ε ≤ Real.exp (2 * p + 7) := by
  have hone : 1 ≤ Real.exp p := Real.one_le_exp hp
  have hseven : (6 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp (7 : ℝ)]
  calc
    1 / externalNetMesh L ε = 3 * (L + 1) * (1 / ε) := by unfold externalNetMesh; field_simp
    _ ≤ 3 * (Real.exp p + Real.exp p) * Real.exp p := by gcongr
    _ = 6 * Real.exp (2 * p) := by rw [two_mul, Real.exp_add]; ring
    _ ≤ Real.exp 7 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right hseven (Real.exp_nonneg _)
    _ = Real.exp (2 * p + 7) := by rw [← Real.exp_add, add_comm]

theorem boxCoverCount_dimension_bound (d : ℕ) (K : ℝ≥0) {B ε p : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hB : B ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) (hinv : 1 / ε ≤ Real.exp p) :
    (((boxCoverMeshCount B K ε + 1) ^ d : ℕ) : ℝ) ≤ Real.exp (p * (3 * p + 4)) := by
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (3 * p + 4)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (boxCoverMeshCount_add_one_le_exp K hB0 hε hp hB hK hinv) d
    _ = Real.exp ((d : ℝ) * (3 * p + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))

theorem exists_externalTestNet_size_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (NO NR dA dZ : ℕ) (KA KZ : ℝ≥0) {BA BZ εA εZ p : ℝ},
      0 ≤ p → 0 ≤ BA → 0 ≤ BZ → 0 < εA → 0 < εZ →
      (NO : ℝ) ≤ Real.exp p → (NR : ℝ) ≤ Real.exp p → (dA : ℝ) ≤ p → (dZ : ℝ) ≤ p →
      BA ≤ Real.exp p → BZ ≤ Real.exp p → (KA : ℝ) ≤ Real.exp p → (KZ : ℝ) ≤ Real.exp p →
      1 / εA ≤ Real.exp p → 1 / εZ ≤ Real.exp p →
      ((NO * (boxCoverMeshCount BA KA εA + 1) ^ dA * NR *
        (boxCoverMeshCount BZ KZ εZ + 1) ^ dZ : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := 2 * X + 2 * X * (3 * X + 4)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro NO NR dA dZ KA KZ BA BZ εA εZ p hp hBA0 hBZ0 hεA hεZ hNO hNR hdA hdZ hBA hBZ hKA hKZ hinvA hinvZ
  have hA := boxCoverCount_dimension_bound dA KA hBA0 hεA hp hdA hBA hKA hinvA
  have hZ := boxCoverCount_dimension_bound dZ KZ hBZ0 hεZ hp hdZ hBZ hKZ hinvZ
  have hpoly : 2 * p + 2 * p * (3 * p + 4) ≤ (p + C) ^ C := by
    simpa [P, X] using hbudget p hp
  push_cast at hA hZ ⊢
  calc
    _ ≤ Real.exp p * Real.exp (p * (3 * p + 4)) * Real.exp p * Real.exp (p * (3 * p + 4)) := by
      gcongr
    _ = Real.exp (2 * p + 2 * p * (3 * p + 4)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hpoly

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bchBoxCover_count_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (B : ℝ≥0) {p ε : ℝ},
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) → 0 < ε → 1 / ε ≤ Real.exp p →
      (((boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε + 1) ^ d : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨A, _, hmetric⟩ := exists_bchBoxMetricConstant_exp_bound s r
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ r + (X + Polynomial.C A) ^ A
  let P := R * (3 * R + 4)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro d H B p ε hp hd hH hB hε hεinv
  let q := p + (p + 2) ^ r + (p + A) ^ A
  have hr : 0 ≤ (p + 2) ^ r := pow_nonneg (by linarith) _
  have hA : 0 ≤ (p + A) ^ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _
  have hpq : p ≤ q := (le_add_of_nonneg_right hr).trans (le_add_of_nonneg_right hA)
  have hrq : (p + 2) ^ r ≤ q := (le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right hA)
  have hAq : (p + A) ^ A ≤ q := le_add_of_nonneg_left (add_nonneg hp hr)
  have hsize := boxCoverCount_dimension_bound d (bchBoxMetricConstant s d H B) B.coe_nonneg hε
    (hp.trans hpq) (hd.trans hpq) (hB.trans (Real.exp_le_exp.mpr hrq))
    ((hmetric d H B p hp hd hH hB).trans (Real.exp_le_exp.mpr hAq))
    (hεinv.trans (Real.exp_le_exp.mpr hpq))
  have hfinal : q * (3 * q + 4) ≤ (p + C) ^ C := by
    simpa [P, R, X, q, Polynomial.eval₂_pow] using hbudget p hp
  exact hsize.trans (Real.exp_le_exp.mpr hfinal)

end Erdos3

end

end OAI
