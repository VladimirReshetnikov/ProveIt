import OAI.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight

namespace OAI

section

namespace Erdos3

open MvPolynomial Module

private theorem integral_C_iff {τ : Type*} (c : ℚ) :
    (C c : MvPolynomial τ ℚ) ∈ integerCoefficientPolynomials τ ↔
      ∃ z : ℤ, c = (z : ℚ) := by
  classical
  constructor
  · intro h
    simpa [MvPolynomial.coeff_C] using
      (mem_integerCoefficientPolynomials_iff _).mp h 0
  · rintro ⟨z, rfl⟩
    exact integerCoefficientPolynomials_C z

private theorem integral_rename_iff {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ ℚ) :
    rename f P ∈ integerCoefficientPolynomials τ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro h
    apply (mem_integerCoefficientPolynomials_iff _).mpr
    intro a
    simpa only [coeff_rename_mapDomain f hf] using
      (mem_integerCoefficientPolynomials_iff _).mp h (a.mapDomain f)
  · intro h
    obtain ⟨Q, hQ⟩ := (mem_integerCoefficientPolynomials P).mp h
    apply (mem_integerCoefficientPolynomials _).mpr
    refine ⟨rename f Q, ?_⟩
    rw [MvPolynomial.map_rename, hQ]

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]
variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)

theorem weightedShearEmbedding_integral_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
    (∀ i, ∃ z : ℤ, x.val.base i = (z : ℚ)) ∧
      x.val.polynomial ∈ integerCoefficientPolynomials σ := by
  have hgen (i : σ ⊕ Unit) : (weightedShearEmbedding w d x).val (X i) =
      shearDerivation x.val (X i) := rfl
  simp only [hgen]
  constructor
  · intro h
    constructor
    · intro i
      exact (integral_C_iff (τ := σ ⊕ Unit) _).mp (by simpa only [shearDerivation_X_inl] using h (Sum.inl i))
    · exact (integral_rename_iff (Sum.inl : σ → σ ⊕ Unit) Sum.inl_injective _).mp (by
        simpa only [shearDerivation_X_inr] using h (Sum.inr ()))
  · rintro ⟨hb, hp⟩ i
    cases i with
    | inl i =>
        rw [shearDerivation_X_inl]
        exact (integral_C_iff _).mpr (hb i)
    | inr u =>
        rw [shearDerivation_X_inr]
        exact (integral_rename_iff Sum.inl Sum.inl_injective _).mpr hp

theorem weightedBasis_integral_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
      ∀ a, ∃ z : ℤ, (weightedBasis w d hw).repr x a = (z : ℚ) := by
  rw [weightedShearEmbedding_integral_iff]
  constructor
  · rintro ⟨hb, hp⟩ a
    cases a with
    | inl i => simpa only [weightedBasis_repr_inl] using hb i
    | inr a => exact (mem_integerCoefficientPolynomials_iff _).mp hp a.val
  · intro h
    constructor
    · intro i
      simpa only [weightedBasis_repr_inl] using h (Sum.inl i)
    · apply (mem_integerCoefficientPolynomials_iff _).mpr
      intro a
      by_cases ha : Finsupp.weight w a < d
      · exact h (Sum.inr ⟨a, ha⟩)
      · refine ⟨0, ?_⟩
        apply not_ne_iff.mp
        intro hc
        have hs := x.property.2 (MvPolynomial.mem_support_iff.mpr hc)
        change Finsupp.weight w a + 1 ≤ d at hs
        omega

variable [Finite (WeightedBasisIndex w d)]

theorem weightedBasis_integralVector_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
      IntegralVector ((weightedBasis w d hw).equivFun x) := by
  rw [weightedBasis_integral_iff w d hw]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩ a
    exact ⟨z a, hz a⟩

theorem weightedBasis_denominatorGrid_iff (B : ℕ) (x : weightedSubalgebra w d) :
    (weightedBasis w d hw).equivFun x ∈ denominatorGrid B ↔
      ∀ i, ((B : ℚ) • weightedShearEmbedding w d x).val (X i) ∈
        integerCoefficientPolynomials (σ ⊕ Unit) := by
  change IntegralVector ((B : ℚ) • (weightedBasis w d hw).equivFun x) ↔ _
  rw [← map_smul]
  simpa only [map_smul] using (weightedBasis_integralVector_iff w d hw ((B : ℚ) • x)).symm

theorem weightedBasis_scaledGrid_normalize (B : ℕ) (hB : 0 < B)
    (x : weightedSubalgebra w d)
    (hx : (weightedBasis w d hw).equivFun x ∈ scaledIntegerGrid B) :
    ∀ i, ((B : ℚ)⁻¹ • weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit) := by
  obtain ⟨z, hz⟩ := hx
  have hBq : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  have hi : IntegralVector ((weightedBasis w d hw).equivFun ((B : ℚ)⁻¹ • x)) := by
    refine ⟨z, ?_⟩
    have hv : (weightedBasis w d hw).equivFun ((B : ℚ)⁻¹ • x) =
        fun i => (z i : ℚ) := by
      rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hBq, one_smul]
    exact congrFun hv
  simpa only [map_smul] using (weightedBasis_integralVector_iff w d hw _).mpr hi

end PolynomialTranslationLie
end Erdos3

end

end OAI
