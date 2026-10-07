import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop

namespace OAI

section

universe level

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ}

theorem finrank_eq_dimension (D : RationalFilteredNilmanifold L s d) :
    finrank ℚ L = d := by
  rw [finrank_eq_card_basis D.basis, Fintype.card_fin]

theorem geometry_finrank_le (D : RationalFilteredNilmanifold L s d) {p : ℝ}
    (hD : D.GeometryComplexityLE p) : (finrank ℚ L : ℝ) ≤ p := by
  rw [D.finrank_eq_dimension]
  exact hD.1

theorem geometry_prod_finrank_le (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p q : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE q) :
    (finrank ℚ (L × M) : ℝ) ≤ p + q := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ M := E.basis.finiteDimensional_of_finite
  rw [finrank_prod, Nat.cast_add]
  exact add_le_add (D.geometry_finrank_le hD) (E.geometry_finrank_le hE)

end RationalFilteredNilmanifold

namespace RationalFilteredNilmanifold

variable {L M : Type level} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ}

theorem geometry_pair_finrank_le (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p q : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE q) :
    (finrank ℚ (PairAlgebra L M) : ℝ) ≤ p + q := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let : FiniteDimensional ℚ M := E.basis.finiteDimensional_of_finite
  let : ∀ i : Bool, Module.Finite ℚ (BoolLieFamily L M i) := by
    intro i
    cases i
    · exact (inferInstance : Module.Finite ℚ M)
    · exact (inferInstance : Module.Finite ℚ L)
  have hpair : finrank ℚ (PairAlgebra L M) = finrank ℚ L + finrank ℚ M := by
    change finrank ℚ (∀ i : Bool, BoolLieFamily L M i) = _
    rw [finrank_pi_fintype, Fintype.sum_bool]
    rfl
  rw [hpair, Nat.cast_add]
  exact add_le_add (D.geometry_finrank_le hD) (E.geometry_finrank_le hE)

end RationalFilteredNilmanifold

theorem two_mul_le_translation_major_budget {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 2 ≤ a) :
    2 * p ≤ (p + (a : ℝ)) ^ a := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hsq : 2 * p ≤ (p + (a : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (p + (a : ℝ) - 1)]
  exact hsq.trans (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + (a : ℝ)) ha)

namespace RationalFilteredNilmanifold

theorem geometry_pair_finrank_le_budget
    {L M : Type level} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    {a : ℕ} (ha : 2 ≤ a) :
    (finrank ℚ (PairAlgebra L M) : ℝ) ≤ (p + (a : ℝ)) ^ a := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hpair : (finrank ℚ (PairAlgebra L M) : ℝ) ≤ 2 * p := by
    simpa only [two_mul] using D.geometry_pair_finrank_le E hD hE
  exact hpair.trans (two_mul_le_translation_major_budget hp ha)

theorem geometry_prod_finrank_le_budget
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    {a : ℕ} (ha : 2 ≤ a) :
    (finrank ℚ (L × M) : ℝ) ≤ (p + (a : ℝ)) ^ a := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hpair : (finrank ℚ (L × M) : ℝ) ≤ 2 * p := by
    simpa only [two_mul] using D.geometry_prod_finrank_le E hD hE
  exact hpair.trans (two_mul_le_translation_major_budget hp ha)

end RationalFilteredNilmanifold

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem card_le_weightedBasisIndex (w : σ → ℕ) (d : ℕ)
    [Fintype (WeightedBasisIndex w d)] :
    Fintype.card σ ≤ Fintype.card (WeightedBasisIndex w d) :=
  Fintype.card_le_of_injective (Sum.inl : σ → WeightedBasisIndex w d) Sum.inl_injective

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

theorem weightedTranslationResidueNilmanifold_base_card_le {p : ℝ}
    (hG : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p) :
    (Fintype.card σ : ℝ) ≤ p :=
  (Nat.cast_le.mpr (card_le_weightedBasisIndex w d)).trans hG.1

theorem weightedTranslationResidueNilmanifold_finrank_le {p : ℝ}
    (hG : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p) :
    (finrank ℚ (weightedSubalgebra w d) : ℝ) ≤ p :=
  (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_finrank_le hG

theorem weightedTranslationResidueNilmanifold_prod_finrank_le
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
    (D : RationalFilteredNilmanifold L t e) {p : ℝ}
    (hG : (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p)
    (hD : D.GeometryComplexityLE p) :
    (finrank ℚ (weightedSubalgebra w d × L) : ℝ) ≤ 2 * p := by
  simpa only [two_mul] using
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_prod_finrank_le D hG hD

end PolynomialTranslationLie
end Erdos3

end

end OAI
