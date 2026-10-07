import OAI.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
import OAI.Combinatorics.Progressions.Linear.KernelScaleIndependence

namespace OAI


namespace Erdos3

open scoped Matrix

noncomputable def coefficientWeight {J : Type*} (f : (J → ℝ) → ℝ)
    (S : J → ℝ) (z : J → ℤ) : ℝ := f (fun j => (z j : ℝ) / S j)

noncomputable def coefficientWeightSum {J : Type*} (f : (J → ℝ) → ℝ) (S : J → ℝ) : ℝ :=
  ∑' z : J → ℤ, coefficientWeight f S z

theorem coefficientWeight_summable {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Summable (coefficientWeight f S) := by
  convert rectangularWeight_summable f (fun _ => 0) S hS hsupport using 1
  funext z
  change f (fun j => (z j : ℝ) / S j) = f (rectangularLatticePoint (fun _ => 0) S z)
  congr 1
  funext j
  simp only [rectangularLatticePoint, sub_zero]

noncomputable def coefficientPMF {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S) :
    PMF (J → ℤ) :=
  realWeightPMF (coefficientWeight f S) (fun _ => hf _)
    (coefficientWeight_summable f S hS hsupport) hZ

noncomputable def coefficientImagePMF {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S) : PMF (I → ℤ) :=
  (coefficientPMF f hf S hS hsupport hZ).map (fun z => A *ᵥ z)

theorem selectedCoefficientEquiv_normalize {I J : Type*} [Fintype I]
    (s : I ↪ J) (S : J → ℝ) (p : (UnselectedColumn s → ℤ) × (I → ℤ)) :
    selectedCoefficientEquiv s ℝ
      ((fun j => (p.1 j : ℝ) / S j.val), (fun i => (p.2 i : ℝ) / S (s i))) =
      fun j => (selectedCoefficientEquiv s ℤ p j : ℝ) / S j := by
  funext j
  obtain ⟨k, rfl⟩ := (selectedFreeFirstEquiv s).surjective j
  simp only [selectedCoefficientEquiv_apply, Equiv.symm_apply_apply]
  cases k <;> rfl

noncomputable def selectedIntegerCoefficientEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) : (I → ℤ) × (UnselectedColumn s → ℤ) ≃ (J → ℤ) :=
  (Equiv.prodComm _ _).trans (selectedCoefficientEquiv s ℤ)

theorem selectedIntegerCoefficient_weight {I J : Type*} [Fintype I]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (S : J → ℝ)
    (p : (I → ℤ) × (UnselectedColumn s → ℤ)) :
    coefficientWeight f S (selectedIntegerCoefficientEquiv s p) =
      scaledIntegerWeight (selectedCoefficientProfile s f)
        (fun i => S (s i)) (fun j => S j.val) p := by
  exact (congrArg f (selectedCoefficientEquiv_normalize s S (p.2, p.1))).symm

theorem selectedCoefficient_weight_sum {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (S : J → ℝ) :
    scaledInputWeightSum (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val) = coefficientWeightSum f S := by
  rw [scaledInputWeightSum, coefficientWeightSum]
  simp only [← selectedIntegerCoefficient_weight]
  exact (selectedIntegerCoefficientEquiv s).tsum_eq _

theorem selectedCoefficient_weight_sum_pos {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hM : 0 < scaledInputMass (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val)) : 0 < coefficientWeightSum f S := by
  rw [← selectedCoefficient_weight_sum s]
  exact scaledInputWeightSum_pos _ _ _ (fun i => hS (s i)) (fun j => hS j.val) hM

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem dependentProductPMF_toMeasure {Q : Type*} [Fintype Q] {X : Q → Type*}
    [∀ q, Countable (X q)] [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSingletonClass (X q)]
    (p : ∀ q, PMF (X q)) :
    (dependentProductPMF p).toMeasure = Measure.pi (fun q => (p q).toMeasure) :=
  Measure.toPMF_toMeasure _

theorem dependentProductPMF_image_law {Q : Type*} [Fintype Q] {X Y : Q → Type*}
    [∀ q, Countable (X q)] [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSingletonClass (X q)]
    [∀ q, Countable (Y q)] [∀ q, MeasurableSpace (Y q)] [∀ q, MeasurableSingletonClass (Y q)]
    (p : ∀ q, PMF (X q)) (F : ∀ q, X q → Y q) (hF : ∀ q, Measurable (F q)) :
    (dependentProductPMF p).toMeasure.map (fun x q => F q (x q)) =
      (dependentProductPMF (fun q => (p q).map (F q))).toMeasure := by
  rw [dependentProductPMF_toMeasure, dependentProductPMF_toMeasure,
    Measure.pi_map_pi (fun q => (hF q).aemeasurable)]
  congr 1
  funext q
  exact PMF.toMeasure_map (F q) (p q) (hF q)

theorem jointCoefficientImage_law {Q : Type*} [Fintype Q] {I J : Q → Type*}
    [∀ q, Fintype (I q)] [∀ q, Fintype (J q)]
    (A : ∀ q, Matrix (I q) (J q) ℤ) (f : ∀ q, (J q → ℝ) → ℝ)
    (hf : ∀ q x, 0 ≤ f q x) (S : ∀ q, J q → ℝ) (hS : ∀ q j, 0 < S q j)
    (R : Q → ℝ) (hsupport : ∀ q x, R q < ‖x‖ → f q x = 0)
    (hZ : ∀ q, 0 < coefficientWeightSum (f q) (S q)) :
    (dependentProductPMF (fun q => coefficientPMF (f q) (hf q) (S q) (hS q)
      (hsupport q) (hZ q))).toMeasure.map (fun x q => A q *ᵥ x q) =
      (dependentProductPMF (fun q => coefficientImagePMF (A q) (f q) (hf q) (S q) (hS q)
        (hsupport q) (hZ q))).toMeasure :=
  dependentProductPMF_image_law _ _ (fun _ => measurable_of_countable _)

end Erdos3


namespace Erdos3

open scoped Matrix

theorem coefficientPMF_apply {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (z : J → ℤ) :
    (coefficientPMF f hf S hS hsupport hZ z).toReal = coefficientWeight f S z / coefficientWeightSum f S :=
  realWeightPMF_apply _ _ _ _ z

theorem selectedCoefficient_input_law {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (hM : 0 < scaledInputMass (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val)) :
    (scaledInputPMF (selectedCoefficientProfile s f) (selectedCoefficientProfile_nonneg s hf)
      (fun i => S (s i)) (fun j => S j.val) (fun i => hS (s i)) (fun j => hS j.val)
      (selectedCoefficientProfile_zero_outside s hsupport) hM).map (selectedIntegerCoefficientEquiv s) =
    coefficientPMF f hf S hS hsupport (selectedCoefficient_weight_sum_pos s f S hS hM) := by
  ext z
  rw [pmf_map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [scaledInputPMF_apply, coefficientPMF_apply, selectedCoefficient_weight_sum]
  rw [← selectedIntegerCoefficient_weight, Equiv.apply_symm_apply]

theorem selectedIntegerCoefficient_mulVec {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) (p : (I → ℤ) × (UnselectedColumn s → ℤ)) :
    A *ᵥ selectedIntegerCoefficientEquiv s p =
      A.submatrix id s *ᵥ p.1 + remainingMatrixColumns A s *ᵥ p.2 := by
  have he : selectedIntegerCoefficientEquiv s p =
      Sum.elim p.1 p.2 ∘ (selectedColumnEquiv s).symm := by
    funext j
    change Sum.elim p.2 p.1 ((Equiv.sumComm _ _) ((selectedColumnEquiv s).symm j)) =
      Sum.elim p.1 p.2 ((selectedColumnEquiv s).symm j)
    cases (selectedColumnEquiv s).symm j <;> rfl
  rw [he]
  have hm := Matrix.submatrix_mulVec_equiv A (Sum.elim p.1 p.2) id (selectedColumnEquiv s)
  rw [← selectedMatrix_fromCols, Matrix.fromCols_mulVec] at hm
  exact hm.symm

theorem selectedCoefficient_image_law {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (hM : 0 < scaledInputMass (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val)) :
    integerImagePMF (A.submatrix id s) (remainingMatrixColumns A s)
      (selectedCoefficientProfile s f) (selectedCoefficientProfile_nonneg s hf)
      (fun i => S (s i)) (fun j => S j.val) (fun i => hS (s i)) (fun j => hS j.val)
      (selectedCoefficientProfile_zero_outside s hsupport) hM =
    coefficientImagePMF A f hf S hS hsupport (selectedCoefficient_weight_sum_pos s f S hS hM) := by
  unfold coefficientImagePMF
  rw [← selectedCoefficient_input_law s f hf S hS hsupport hM, PMF.map_comp]
  unfold integerImagePMF
  congr 1
  funext p
  exact (selectedIntegerCoefficient_mulVec A s p).symm

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped BigOperators

def spatialCoordinateArrayEquiv (K X : Type*) : (K × X → ℤ) ≃ (X → K → ℤ) where
  toFun z x k := z (k, x)
  invFun z p := z p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem shiftedSmoothProductMass_grouped {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z) :
    shiftedSmoothProductMass a S =
      ∏ x, shiftedSmoothProductMass (fun k => a (k, x)) (fun k => S (k, x)) := by
  rw [shiftedSmoothProductMass_eq_prod a S hS]
  simp_rw [shiftedSmoothProductMass_eq_prod _ _ (fun k => hS (k, _))]
  rw [Fintype.prod_prod_type]
  exact Finset.prod_comm

theorem shiftedSmoothProductMass_slice_pos {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z)
    (hZ : 0 < shiftedSmoothProductMass a S) (x : X) :
    0 < shiftedSmoothProductMass (fun k => a (k, x)) (fun k => S (k, x)) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun k => hS (k, x))]
  exact Finset.prod_pos (fun k _ => shiftedSmoothProductMass_coordinate_pos a S hS hZ (k, x))

theorem shiftedSmoothProductPMF_grouped {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (spatialCoordinateArrayEquiv K X) =
      dependentProductPMF (fun x => shiftedSmoothProductPMF
        (fun k => a (k, x)) (fun k => S (k, x)) (fun k => hS (k, x))
        (shiftedSmoothProductMass_slice_pos a S hS hZ x)) := by
  ext z
  have hm := pmf_map_injective_at (shiftedSmoothProductPMF a S hS hZ)
    (spatialCoordinateArrayEquiv K X) (spatialCoordinateArrayEquiv K X).injective
    ((spatialCoordinateArrayEquiv K X).symm z)
  rw [Equiv.apply_symm_apply] at hm
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [hm, shiftedSmoothProductPMF_toReal, dependentProductPMF_apply, ENNReal.toReal_prod]
  simp_rw [shiftedSmoothProductPMF_toReal]
  rw [Finset.prod_div_distrib, shiftedSmoothProductMass_grouped a S hS]
  congr 1
  simp only [rectangularWeight, smoothProductProfile, rectangularLatticePoint,
    spatialCoordinateArrayEquiv, Equiv.coe_fn_symm_mk, Fintype.prod_prod_type]
  exact Finset.prod_comm

theorem shiftedSmoothProductPMF_grouped_expectation {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (φ : (K × X → ℤ) → ℂ) :
    (∑' z, ((shiftedSmoothProductPMF a S hS hZ z).toReal : ℂ) * φ z) =
      ∑' z, ((dependentProductPMF (fun x => shiftedSmoothProductPMF
        (fun k => a (k, x)) (fun k => S (k, x)) (fun k => hS (k, x))
        (shiftedSmoothProductMass_slice_pos a S hS hZ x)) z).toReal : ℂ) *
          φ ((spatialCoordinateArrayEquiv K X).symm z) := by
  rw [← shiftedSmoothProductPMF_grouped a S hS hZ,
    pmf_map_injective_expectation _ _ (spatialCoordinateArrayEquiv K X).injective]
  simp only [Equiv.symm_apply_apply]

theorem dependentProductPMF_map_of_image_law {Q : Type*} [Fintype Q] {X Y : Q → Type*}
    [∀ q, Countable (X q)] [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSingletonClass (X q)]
    [∀ q, Countable (Y q)] [∀ q, MeasurableSpace (Y q)] [∀ q, MeasurableSingletonClass (Y q)]
    (p : ∀ q, PMF (X q)) (F : ∀ q, X q → Y q) :
    (dependentProductPMF p).map (fun x q => F q (x q)) =
      dependentProductPMF (fun q => (p q).map (F q)) := by
  let f : (∀ q, X q) → (∀ q, Y q) := fun x q => F q (x q)
  have h : (dependentProductPMF p).toMeasure.map f =
      (dependentProductPMF (fun q => (p q).map (F q))).toMeasure :=
    dependentProductPMF_image_law p F (fun _ => measurable_of_countable _)
  rw [PMF.toMeasure_map f (dependentProductPMF p) (measurable_of_countable f)] at h
  exact PMF.toMeasure_injective h

end Erdos3

end OAI
