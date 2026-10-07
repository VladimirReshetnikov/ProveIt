import OAI.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_real_kernel_generators {J V : Type*} [Fintype J] [Fintype V]
    (A : Matrix V J ℚ) {H : ℕ} (hH : 1 ≤ H) (hA : ∀ v j, RationalHeightLE (A v j) H) :
    ∃ P : Matrix J J ℚ,
      (∀ i j, RationalHeightLE (P i j) (imageDefiningHeight (Fintype.card V) (Fintype.card V) H)) ∧
      LinearMap.range (Matrix.of (fun i j => (P i j : ℝ))).mulVecLin =
        LinearMap.ker (Matrix.of (fun v j => (A v j : ℝ))).mulVecLin := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  let P : Matrix J J ℚ := 1 - S * A
  have hSr := real_matrix_image_section A S hS
  have hPr : Matrix.of (fun i j => (P i j : ℝ)) =
      1 - Matrix.of (fun i v => (S i v : ℝ)) * Matrix.of (fun v j => (A v j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [P, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨P, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix J J ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul S A hSH hA i j
    simpa only [P, Matrix.sub_apply, imageDefiningHeight, mul_one, one_mul, mul_comm] using hI.sub hprod
  · ext x
    change (∃ y, Matrix.of (fun i j => (P i j : ℝ)) *ᵥ y = x) ↔
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [hPr]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSr,
        sub_self, Matrix.zero_mulVec]
    · intro hx
      refine ⟨x, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

def jointSpaceGeneratorHeight (ambient columns rows H R : ℕ) : ℕ :=
  imageDefiningHeight (ambient + rows) (ambient + rows)
    (max (imageDefiningHeight columns ambient H) R)

namespace VectorPolynomial

theorem exists_jointRationalSpace_generators {J C V : Type*}
    [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (hA : ∀ v j, RationalHeightLE (A v j) R) :
    ∃ P : Matrix J J ℚ,
      (∀ i j, RationalHeightLE (P i j)
        (jointSpaceGeneratorHeight (Fintype.card J) (Fintype.card C) (Fintype.card V) H R)) ∧
      LinearMap.range (Matrix.of (fun i j => (P i j : ℝ))).mulVecLin = jointRationalSpace B A := by
  obtain ⟨Q, hQ, hQker⟩ := exists_real_span_defining_matrix B hH hB
  let A' : Matrix (J ⊕ V) J ℚ := Matrix.of (fun v j => Sum.elim (fun i => Q i j) (fun v => A v j) v)
  have hA' : ∀ v j, RationalHeightLE (A' v j) (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R) := by
    intro v j
    cases v with
    | inl i => exact (hQ i j).mono (le_max_left _ _)
    | inr v => exact (hA v j).mono (le_max_right _ _)
  obtain ⟨P, hP, hPker⟩ := exists_real_kernel_generators A' (hR.trans (le_max_right _ _)) hA'
  refine ⟨P, ?_, hPker.trans ?_⟩
  · simpa only [Fintype.card_sum, jointSpaceGeneratorHeight] using hP
  · ext x
    change LinearMap.ker (Matrix.of (fun i j => (Q i j : ℝ))).mulVecLin =
      LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin at hQker
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      x ∈ LinearMap.range (Matrix.of (fun i j => (B i j : ℝ))).mulVecLin ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [← hQker]
    change (Matrix.of (fun v j => (A' v j : ℝ)) *ᵥ x = 0) ↔
      (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0) ∧
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    constructor
    · intro hx
      exact ⟨funext (fun i => congrFun hx (.inl i)), funext (fun v => congrFun hx (.inr v))⟩
    · rintro ⟨hQx, hAx⟩
      ext v
      cases v with
      | inl i => exact congrFun hQx i
      | inr v => exact congrFun hAx v

end VectorPolynomial

theorem jointSpaceGeneratorHeight_le_exp (ambient columns rows H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p) (hr : (rows : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    (jointSpaceGeneratorHeight ambient columns rows H R : ℝ) ≤ Real.exp ((p + 2) ^ 120) := by
  have hfirst := imageDefiningHeight_le_exp columns ambient H hp hc ha hH
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have hmax : ((max (imageDefiningHeight columns ambient H) R : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
    rw [Nat.cast_max]
    exact max_le hfirst (hR.trans (Real.exp_le_exp.mpr hpp))
  have hsum : ((ambient + rows : ℕ) : ℝ) ≤ (p + 2) ^ 10 := by
    have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ 10 := pow_le_pow_right₀ (by linarith) (by decide)
    push_cast
    nlinarith
  have hsecond := imageDefiningHeight_le_exp (ambient + rows) (ambient + rows)
    (max (imageDefiningHeight columns ambient H) R) (by positivity) hsum hsum hmax
  exact hsecond.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 10))

end Erdos3

end

end OAI
