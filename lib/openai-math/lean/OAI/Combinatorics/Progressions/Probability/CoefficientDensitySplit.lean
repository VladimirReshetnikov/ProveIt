import OAI.Combinatorics.Progressions.Estimates.JoinedCoefficientProfile
import OAI.Combinatorics.Progressions.Geometry.SplitFreeCoordinates

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

noncomputable def selectedSplitCoefficients {I J N : Type*} [Fintype I]
    (s : I ↪ J) (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) : J ⊕ N → ℝ :=
  Sum.elim (selectedCoefficientEquiv s ℝ ((fun j => p.1 (.inl j)), p.2))
    (fun n => p.1 (.inr n))

theorem selectedSplitCoefficients_measurable {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) :
    Measurable (selectedSplitCoefficients (N := N) s) := by
  change Measurable ((MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm ∘
    (Prod.map (selectedCoefficientMeasurableEquiv s) id ∘
      splitFreeCoordinates I (UnselectedColumn s) N))
  exact (MeasurableEquiv.measurable _).comp
    (((selectedCoefficientMeasurableEquiv s).measurable.prodMap measurable_id).comp
      (splitFreeCoordinates I (UnselectedColumn s) N).measurable)

theorem selectedSplitCoefficients_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J)
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f) (hgi : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (realDensityMeasure volume (splitFreeProfile (selectedCoefficientProfile s f) g)).map
        (selectedSplitCoefficients s) =
      realDensityMeasure volume (joinedCoefficientProfile f g) := by
  let : IsFiniteMeasure (realDensityMeasure volume (selectedCoefficientProfile s f)) :=
    realDensityMeasure_finite _ _ (selectedCoefficientProfile_integrable s hfi)
      (selectedCoefficientProfile_nonneg s hf0)
  let : IsFiniteMeasure (realDensityMeasure volume g) := realDensityMeasure_finite _ _ hgi hg0
  have hsel : Measurable (selectedCoefficientProfile s f) :=
    hf.comp (selectedCoefficientMeasurableEquiv s).measurable
  have hprod := (selectedCoefficientMeasurableEquiv s).measurable.prodMap
    (measurable_id : Measurable (id : (N → ℝ) → (N → ℝ)))
  change Measure.map ((MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm ∘
    (Prod.map (selectedCoefficientMeasurableEquiv s) id ∘
      splitFreeCoordinates I (UnselectedColumn s) N)) _ = _
  rw [← Measure.map_map (MeasurableEquiv.measurable _) (hprod.comp (MeasurableEquiv.measurable _)),
    ← Measure.map_map hprod (MeasurableEquiv.measurable _),
    splitFreeProfile_measure _ _ hsel hg (selectedCoefficientProfile_nonneg s hf0),
    ← Measure.map_prod_map _ _ (selectedCoefficientMeasurableEquiv s).measurable measurable_id,
    selectedCoefficientProfile_measure s f, Measure.map_id,
    joinedCoefficientProfile_measure f g hf hg hf0]

theorem selectedSplitCoefficients_matrix {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℝ) (C : Matrix I N ℝ) (s : I ↪ J)
    (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) :
    Matrix.fromCols A C *ᵥ selectedSplitCoefficients s p =
      A.submatrix id s *ᵥ p.2 + remainingMatrixColumns A s *ᵥ (fun j => p.1 (.inl j)) +
        C *ᵥ (fun n => p.1 (.inr n)) := by
  rw [Matrix.fromCols_mulVec]
  change A *ᵥ selectedCoefficientEquiv s ℝ ((fun j => p.1 (.inl j)), p.2) + _ = _
  rw [selectedCoefficient_matrix_apply]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem selectedSplitCoefficients_normalized_matrix {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) :
    normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ selectedSplitCoefficients s p =
      normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP p.2 +
        splitFreeColumns
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
          (matrixSupCLM (normalizedIntegerColumns C T P)) p.1 := by
  have he (x : I → ℝ) :
      normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP x =
        normalizedIntegerPivot (A.submatrix id s) (fun i => S (s i)) P *ᵥ x := by
    change (normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap x = _
    rw [normalizedPivotEquiv_coe, matrixSupCLM_apply]
  rw [normalizedIntegerColumns_fromCols, selectedSplitCoefficients_matrix,
    normalizedIntegerColumns_submatrix, ← normalized_remainingMatrixColumns,
    he, splitFreeColumns_apply, matrixSupCLM_apply, matrixSupCLM_apply]
  exact add_assoc _ _ _

theorem coefficientSplitDensity_law {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g)
    {R Q : ℝ} (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ y, Q < ‖y‖ → g y = 0)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    (realDensityMeasure volume (joinedCoefficientProfile f g)).map
      (fun x => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ x) =
      realDensityMeasure volume
        (pivotOutputDensity
          (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
          (splitFreeColumns
            (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
            (matrixSupCLM (normalizedIntegerColumns C T P)))
          (splitFreeProfile (selectedCoefficientProfile s f) g)) := by
  have hF : Measurable (fun x => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ x) :=
    (matrixSupCLM _).continuous.measurable
  have hsel : Continuous (selectedCoefficientProfile s f) :=
    hf.comp (selectedCoefficientEquiv_lipschitz s).continuous
  rw [← selectedSplitCoefficients_law s f g hf.measurable hg.measurable
    (compactBox_integrable f hf R hfs) (compactBox_integrable g hg Q hgs) hf0 hg0,
    Measure.map_map hF (selectedSplitCoefficients_measurable s)]
  have he := funext (selectedSplitCoefficients_normalized_matrix A C s hA S T P hS hP)
  change (fun p => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ
    selectedSplitCoefficients s p) = _ at he
  rw [show (fun x => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ x) ∘
      selectedSplitCoefficients s = _ from he]
  exact pivotOutputDensity_law _ _
    (splitFreeProfile_integrable hsel hg (selectedCoefficientProfile_zero_outside s hfs) hgs)
    (splitFreeProfile_nonneg (selectedCoefficientProfile_nonneg s hf0) hg0)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientDensity_split {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (hfull : ((Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl)).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (R Q H V K L : ℝ≥0)
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfr : ∀ x, f x ∈ Set.Icc (0 : ℝ) H) (hgr : ∀ y, g y ∈ Set.Icc (0 : ℝ) V)
    (hfs : ∀ x, (R : ℝ) < ‖x‖ → f x = 0) (hgs : ∀ y, (Q : ℝ) < ‖y‖ → g y = 0) :
    selectedCoefficientDensity (Matrix.fromCols A C) (s.trans Function.Embedding.inl) hfull
      (Sum.elim S T) P (Sum.rec hS hT) hP (joinedCoefficientProfile f g) =
      pivotOutputDensity
        (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
        (splitFreeColumns
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
          (matrixSupCLM (normalizedIntegerColumns C T P)))
        (splitFreeProfile (selectedCoefficientProfile s f) g) := by
  have hj := joinedCoefficientProfile_lipschitz H V K L hf hg hfr hgr
  have hjs := joinedCoefficientProfile_zero_outside hfs hgs
  have hfcap : ∀ x, ‖f x‖ ≤ H := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfr x).1]
    exact (hfr x).2
  have hgcap : ∀ y, ‖g y‖ ≤ V := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hgr y).1]
    exact (hgr y).2
  have hsplit := splitFreeProfile_lipschitz (selectedCoefficientProfile_lipschitz s hf) hg
    (selectedCoefficientProfile_norm_le s hfcap) hgcap
  have hss := splitFreeProfile_zero_outside (selectedCoefficientProfile_zero_outside s hfs) hgs
  have hj0 := joinedCoefficientProfile_nonneg (fun x => (hfr x).1) (fun y => (hgr y).1)
  have hs0 := splitFreeProfile_nonneg (selectedCoefficientProfile_nonneg s (fun x => (hfr x).1))
    (fun y => (hgr y).1)
  apply continuousDensity_eq_of_measure_eq
    (pivotOutputDensity_lipschitz _ _ (max R Q) _
      (selectedCoefficientProfile_lipschitz _ hj) (selectedCoefficientProfile_zero_outside _ hjs)).continuous
    (pivotOutputDensity_lipschitz _ _ (max R Q) _ hsplit hss).continuous
    (pivotOutputDensity_nonneg _ _ (selectedCoefficientProfile_nonneg _ hj0))
    (pivotOutputDensity_nonneg _ _ hs0)
  exact (selectedCoefficientDensity_law _ _ hfull (Sum.elim S T) P (Sum.rec hS hT) hP _
    (joinedCoefficientProfile_integrable
      (compactBox_integrable f hf.continuous R hfs) (compactBox_integrable g hg.continuous Q hgs)) hj0).symm.trans
    (coefficientSplitDensity_law A C s hA S T P hS hP f g hf.continuous hg.continuous hfs hgs
      (fun x => (hfr x).1) (fun y => (hgr y).1))

end Erdos3

end

end OAI
