import OAI.Combinatorics.Progressions.Estimates.CoefficientRowReindex

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def selectedCoefficientMeasurableEquiv {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : (UnselectedColumn s → ℝ) × (I → ℝ) ≃ᵐ (J → ℝ) where
  toEquiv := selectedCoefficientEquiv s ℝ
  measurable_toFun := (selectedCoefficientEquiv_lipschitz s).continuous.measurable
  measurable_invFun := by
    change Measurable (fun x : J → ℝ => ((fun j : UnselectedColumn s => x j.val), fun i => x (s i)))
    fun_prop

theorem selectedCoefficientMeasurableEquiv_preserving {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : MeasurePreserving (selectedCoefficientMeasurableEquiv s) volume volume := by
  have hm := (volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) (selectedFreeFirstEquiv s)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : UnselectedColumn s ⊕ I => ℝ))
  convert hm using 1
  funext p j
  simp only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', Equiv.coe_fn_symm_mk, eq_rec_constant]
  rfl

theorem selectedCoefficientProfile_measure {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) :
    (realDensityMeasure volume (selectedCoefficientProfile s f)).map (selectedCoefficientMeasurableEquiv s) =
      realDensityMeasure volume f := by
  rw [realDensityMeasure_map_equiv, (selectedCoefficientMeasurableEquiv_preserving s).map_eq]
  congr 1
  funext x
  change f ((selectedCoefficientMeasurableEquiv s) ((selectedCoefficientMeasurableEquiv s).symm x)) = f x
  rw [MeasurableEquiv.apply_symm_apply]

theorem selectedCoefficientProfile_integrable {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (selectedCoefficientProfile s f) :=
  (selectedCoefficientMeasurableEquiv_preserving s).integrable_comp_of_integrable hf

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem selectedCoefficient_matrix_apply {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (A : Matrix I J R) (s : I ↪ J) (p : (UnselectedColumn s → R) × (I → R)) :
    A *ᵥ selectedCoefficientEquiv s R p =
      A.submatrix id s *ᵥ p.2 + remainingMatrixColumns A s *ᵥ p.1 := by
  have he : selectedCoefficientEquiv s R p = Sum.elim p.2 p.1 ∘ (selectedColumnEquiv s).symm := by
    funext j
    change Sum.elim p.1 p.2 ((Equiv.sumComm _ _) ((selectedColumnEquiv s).symm j)) =
      Sum.elim p.2 p.1 ((selectedColumnEquiv s).symm j)
    cases (selectedColumnEquiv s).symm j <;> rfl
  rw [he]
  have hm := Matrix.submatrix_mulVec_equiv A (Sum.elim p.2 p.1) id (selectedColumnEquiv s)
  rw [← selectedMatrix_fromCols, Matrix.fromCols_mulVec] at hm
  exact hm.symm

theorem selectedCoefficientDensity_law {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure volume f).map (fun x => normalizedIntegerColumns A S P *ᵥ x) =
      realDensityMeasure volume (selectedCoefficientDensity A s hA S P hS hP f) := by
  classical
  have hmap : (fun p : (UnselectedColumn s → ℝ) × (I → ℝ) =>
      normalizedIntegerPivot (A.submatrix id s) (fun i => S (s i)) P *ᵥ p.2 +
        normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P *ᵥ p.1) =
      (fun x => normalizedIntegerColumns A S P *ᵥ x) ∘ selectedCoefficientMeasurableEquiv s := by
    funext p
    change _ = normalizedIntegerColumns A S P *ᵥ selectedCoefficientEquiv s ℝ p
    rw [selectedCoefficient_matrix_apply, normalizedIntegerColumns_submatrix,
      ← normalized_remainingMatrixColumns]
  have hF : Measurable (fun x => normalizedIntegerColumns A S P *ᵥ x) :=
    (matrixSupCLM (normalizedIntegerColumns A S P)).continuous.measurable
  rw [← selectedCoefficientProfile_measure s f,
    Measure.map_map hF
      (selectedCoefficientMeasurableEquiv s).measurable, ← hmap]
  exact normalizedFiberDensity_law _ _ _ _ _ _ _ _
    (selectedCoefficientProfile_integrable s hf) (selectedCoefficientProfile_nonneg s hf0)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem selectedCoefficientEquiv_sub {I J : Type*} [Fintype I]
    (s : I ↪ J) (p q : (UnselectedColumn s → ℝ) × (I → ℝ)) :
    selectedCoefficientEquiv s ℝ (p - q) =
      selectedCoefficientEquiv s ℝ p - selectedCoefficientEquiv s ℝ q := by
  funext j
  simp only [selectedCoefficientEquiv_apply, Pi.sub_apply]
  cases (selectedFreeFirstEquiv s).symm j <;> rfl

theorem selectedCoefficientProfile_input_translate {I J : Type*} [Fintype I]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (a : J → ℝ) :
    selectedCoefficientProfile s (fun x => f (x - a)) =
      fun p => selectedCoefficientProfile s f (p - (selectedCoefficientEquiv s ℝ).symm a) := by
  funext p
  simp only [selectedCoefficientProfile, Function.comp_apply, selectedCoefficientEquiv_sub,
    Equiv.apply_symm_apply]

theorem selectedCoefficientDensity_input_translate {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (a : J → ℝ) (v : I → ℝ) :
    selectedCoefficientDensity M s hM S P hS hP (fun x => f (x - a)) v =
      selectedCoefficientDensity M s hM S P hS hP f
        (v - normalizedIntegerColumns M S P *ᵥ a) := by
  let E := normalizedPivotEquiv (M.submatrix id s) hM (fun i => S (s i)) P (fun i => hS (s i)) hP
  let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) P)
  let b := (selectedCoefficientEquiv s ℝ).symm a
  have hmap : normalizedIntegerColumns M S P *ᵥ a = E b.2 + F b.1 := by
    have h := selectedCoefficient_matrix_apply (normalizedIntegerColumns M S P) s b
    rw [Equiv.apply_symm_apply, normalizedIntegerColumns_submatrix, ← normalized_remainingMatrixColumns] at h
    change _ = (E.toContinuousLinearMap b.2) + F b.1
    rw [show E.toContinuousLinearMap = matrixSupCLM
      (normalizedIntegerPivot (M.submatrix id s) (fun i => S (s i)) P) from
      normalizedPivotEquiv_coe _ _ _ _ _ _, matrixSupCLM_apply]
    exact h
  unfold selectedCoefficientDensity normalizedFiberDensity
  rw [selectedCoefficientProfile_input_translate, pivotOutputDensity_input_translate]
  change pivotOutputDensity E F (selectedCoefficientProfile s f) (v - (E b.2 + F b.1)) = _
  rw [← hmap]

end Erdos3

end

section

namespace Erdos3

theorem selectedCoefficientDensity_normalized_congr {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S₁ S₂ : J → ℝ) (P₁ P₂ : I → ℝ)
    (hS₁ : ∀ j, 0 < S₁ j) (hS₂ : ∀ j, 0 < S₂ j)
    (hP₁ : ∀ i, 0 < P₁ i) (hP₂ : ∀ i, 0 < P₂ i)
    (he : normalizedIntegerColumns M S₁ P₁ = normalizedIntegerColumns M S₂ P₂)
    (f : (J → ℝ) → ℝ) :
    selectedCoefficientDensity M s hM S₁ P₁ hS₁ hP₁ f =
      selectedCoefficientDensity M s hM S₂ P₂ hS₂ hP₂ f := by
  have hp := congrArg (fun A : Matrix I J ℝ => A.submatrix id s) he
  rw [normalizedIntegerColumns_submatrix, normalizedIntegerColumns_submatrix] at hp
  have hequiv : normalizedPivotEquiv (M.submatrix id s) hM
      (fun i => S₁ (s i)) P₁ (fun i => hS₁ (s i)) hP₁ =
      normalizedPivotEquiv (M.submatrix id s) hM
        (fun i => S₂ (s i)) P₂ (fun i => hS₂ (s i)) hP₂ := by
    ext v i
    change ((normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap v) i =
      ((normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap v) i
    rw [normalizedPivotEquiv_coe, normalizedPivotEquiv_coe, hp]
  unfold selectedCoefficientDensity normalizedFiberDensity
  rw [hequiv, normalized_remainingMatrixColumns, normalized_remainingMatrixColumns, he]

end Erdos3

end

end OAI
