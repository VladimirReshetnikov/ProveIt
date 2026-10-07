import OAI.Combinatorics.Progressions.Geometry.WeightedTranslationBufferedCoordinates

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def baseRealElement (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (b : σ → ℝ) : ℝ ⊗[ℚ] weightedSubalgebra w d := by
  letI := weightedBasisIndex_finite w d hw
  exact ((weightedBasis w d hw).baseChange ℝ).equivFun.symm (Sum.elim b (fun _ => 0))

noncomputable def polynomialRealElement (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) : ℝ ⊗[ℚ] weightedSubalgebra w d := by
  letI := weightedBasisIndex_finite w d hw
  exact ((weightedBasis w d hw).baseChange ℝ).equivFun.symm
    (Sum.elim (fun _ => 0) (fun a => P.val.coeff a.val))

@[simp] theorem baseRealElement_repr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (b : σ → ℝ) (a : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr (baseRealElement w d hw b) a =
      Sum.elim b (fun _ => 0) a := by
  let := weightedBasisIndex_finite w d hw
  exact congrFun (((weightedBasis w d hw).baseChange ℝ).equivFun.apply_symm_apply _) a

@[simp] theorem polynomialRealElement_repr (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) (a : WeightedBasisIndex w d) :
    ((weightedBasis w d hw).baseChange ℝ).repr (polynomialRealElement w d hw P) a =
      Sum.elim (fun _ => 0) (fun a => P.val.coeff a.val) a := by
  let := weightedBasisIndex_finite w d hw
  exact congrFun (((weightedBasis w d hw).baseChange ℝ).equivFun.apply_symm_apply _) a

theorem realShearEmbedding_base_coeff (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (i : σ) :
    ((realShearEmbedding w d x).val (X (Sum.inl i))).coeff 0 =
      ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inl i) := by
  let a : PolynomialShearIndex (shearWeight w d) := ⟨Sum.inl i, 0, by
    change Finsupp.weight (shearWeight w d) 0 + 1 ≤ w i
    simpa using Nat.succ_le_of_lt (hw i)⟩
  change (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a = _
  rw [realShearEmbedding_repr]
  apply realificationLieHom_repr_coordinate (weightedBasis w d hw) _ _ a (Sum.inl i) _ x
  intro y
  rw [polynomialShearBasis_repr, weightedBasis_repr_inl]
  change (shearDerivation y.val (X (Sum.inl i))).coeff 0 = _
  rw [shearDerivation_X_inl]
  simp

theorem realShearEmbedding_extra_coeff (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    ((realShearEmbedding w d x).val (X (Sum.inr ()))).coeff (a.val.mapDomain Sum.inl) =
      ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inr a) := by
  have hweight : Finsupp.weight (shearWeight w d) (a.val.mapDomain Sum.inl) =
      Finsupp.weight w a.val := by
    change Finsupp.linearCombination ℕ (shearWeight w d) (a.val.mapDomain Sum.inl) = _
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  let j : PolynomialShearIndex (shearWeight w d) := ⟨Sum.inr (), a.val.mapDomain Sum.inl, by
    change Finsupp.weight (shearWeight w d) (a.val.mapDomain Sum.inl) + 1 ≤ d
    rw [hweight]
    exact a.property⟩
  change (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) j = _
  rw [realShearEmbedding_repr]
  apply realificationLieHom_repr_coordinate (weightedBasis w d hw) _ _ j (Sum.inr a) _ x
  intro y
  rw [polynomialShearBasis_repr, weightedBasis_repr_inr]
  change (shearDerivation y.val (X (Sum.inr ()))).coeff (a.val.mapDomain Sum.inl) = _
  rw [shearDerivation_X_inr, coeff_rename_mapDomain Sum.inl Sum.inl_injective]

theorem realShearEmbedding_polynomial_mem (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (P : MvPolynomial σ ℝ)
    (hP : (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P) :
    P ∈ weightedSupportLT w d := by
  intro a ha
  have hcoeff : ((realShearEmbedding w d x).val (X (Sum.inr ()))).coeff
      (a.mapDomain Sum.inl) ≠ 0 := by
    rw [hP, coeff_rename_mapDomain Sum.inl Sum.inl_injective]
    exact MvPolynomial.mem_support_iff.mp ha
  have h := (realShearEmbedding w d x).property (Sum.inr ())
    (MvPolynomial.mem_support_iff.mpr hcoeff)
  change Finsupp.weight (shearWeight w d) (a.mapDomain Sum.inl) + 1 ≤ d at h
  change Finsupp.weight w a < d
  change Finsupp.linearCombination ℕ (shearWeight w d) (a.mapDomain Sum.inl) + 1 ≤ d at h
  rw [Finsupp.linearCombination_mapDomain] at h
  exact h

theorem realShearEmbedding_shape_of_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    (b : σ → ℝ) (P : weightedSupportLT (R := ℝ) w d)
    (hb : ∀ i, ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inl i) = b i)
    (hP : ∀ a, ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inr a) = P.val.coeff a.val) :
    (∀ i, (realShearEmbedding w d x).val (X (Sum.inl i)) = C (b i)) ∧
      (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P.val := by
  classical
  obtain ⟨b', P', hb', hP'⟩ := realShearEmbedding_shape w d x
  have hbq (i : σ) : b' i = b i := by
    have h := realShearEmbedding_base_coeff w d hw x i
    rw [hb', hb] at h
    simpa using h
  have hPq : P' = P.val := by
    have hmem := realShearEmbedding_polynomial_mem w d x P' hP'
    apply MvPolynomial.ext
    intro a
    by_cases ha : Finsupp.weight w a < d
    · have h := realShearEmbedding_extra_coeff w d hw x ⟨a, ha⟩
      rw [hP', coeff_rename_mapDomain Sum.inl Sum.inl_injective, hP] at h
      exact h
    · have hz (Q : MvPolynomial σ ℝ) (hQ : Q ∈ weightedSupportLT w d) : Q.coeff a = 0 := by
        by_contra hc
        exact ha (hQ (MvPolynomial.mem_support_iff.mpr hc))
      rw [hz P' hmem, hz P.val P.property]
  exact ⟨fun i => (hb' i).trans (congrArg C (hbq i)), hP'.trans (congrArg (rename Sum.inl) hPq)⟩

theorem baseRealElement_shear_base (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (b : σ → ℝ) (i : σ) :
    (realShearEmbedding w d (baseRealElement w d hw b)).val (X (Sum.inl i)) = C (b i) :=
  (realShearEmbedding_shape_of_coordinates w d hw _ b 0 (by simp) (by simp)).1 i

theorem baseRealElement_shear_extra (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (b : σ → ℝ) :
    (realShearEmbedding w d (baseRealElement w d hw b)).val (X (Sum.inr ())) = 0 := by
  simpa using (realShearEmbedding_shape_of_coordinates w d hw
    (baseRealElement w d hw b) b 0 (by simp) (by simp)).2

theorem polynomialRealElement_shear_base (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) (i : σ) :
    (realShearEmbedding w d (polynomialRealElement w d hw P)).val (X (Sum.inl i)) = 0 := by
  simpa using (realShearEmbedding_shape_of_coordinates w d hw
    (polynomialRealElement w d hw P) 0 P (by simp) (by simp)).1 i

theorem polynomialRealElement_shear_extra (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) :
    (realShearEmbedding w d (polynomialRealElement w d hw P)).val (X (Sum.inr ())) =
      rename Sum.inl P.val :=
  (realShearEmbedding_shape_of_coordinates w d hw _ 0 P (by simp) (by simp)).2

end Erdos3.PolynomialTranslationLie

end

end OAI
