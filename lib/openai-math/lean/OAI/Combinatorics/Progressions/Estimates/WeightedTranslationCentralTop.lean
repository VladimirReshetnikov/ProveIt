import OAI.Combinatorics.Progressions.Lattices.WeightedTranslationCentralLattice

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

@[simp] theorem centralRealLine_coord (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    (centralRealLine w d hw hd hwd t).coord =
      t ⊗ₜ[ℚ] centralRationalElement w d hd 1 := by
  classical
  apply ((weightedBasis w d hw).baseChange ℝ).repr.injective
  ext a
  change ((weightedBasis w d hw).baseChange ℝ).repr
    (polynomialRealElement w d hw (centralConstantPolynomial w d hd t)) a = _
  rw [polynomialRealElement_repr, Basis.baseChange_repr_tmul]
  cases a with
  | inl i => simp [weightedBasis_repr_inl, centralRationalElement]
  | inr a =>
    simp only [Sum.elim_inr, centralConstantPolynomial, weightedBasis_repr_inr,
      centralRationalElement, coeff_C]
    split_ifs <;> simp

 theorem centralRationalElement_mem_top (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    centralRationalElement w d hd q ∈ (weightedFiltration w d hwd).layer d := by
  refine ⟨fun i hi => rfl, ?_⟩
  exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

 theorem centralRealLine_mem_top (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    centralRealLine w d hw hd hwd t ∈
      (weightedFiltration w d hwd).realification.subgroup d := by
  change (centralRealLine w d hw hd hwd t).coord ∈
    (weightedFiltration w d hwd).realLayer d
  rw [centralRealLine_coord]
  exact LieSubmodule.tmul_mem_baseChange_of_mem t
    (centralRationalElement_mem_top w d hd hwd 1)

end Erdos3.PolynomialTranslationLie

end

end OAI
