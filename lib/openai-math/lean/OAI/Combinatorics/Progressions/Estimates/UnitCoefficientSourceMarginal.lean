/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import Mathlib.Probability.Independence.Basic
import OAI.Combinatorics.Progressions.Lattices.IntegerMatrixRealDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def unitCoefficientSource (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  realDensityMeasure volume (smoothProductProfile I)

instance unitCoefficientSource_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (unitCoefficientSource I) :=
  realDensityMeasure_probability volume _
    ((smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport (smoothProductProfile_compact I))
    (fun r => (smoothProductProfile_range I r).1) (smoothProductProfile_integral I)

theorem unitCoefficientSource_norm_le (I : Type*) [Fintype I] :
    ∀ᵐ r ∂unitCoefficientSource I, ‖r‖ ≤ 1 := by
  have hi : Integrable (smoothProductProfile I) := (smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport
    (smoothProductProfile_compact I)
  have hnull : unitCoefficientSource I {r | 1 < ‖r‖} = 0 := by
    rw [unitCoefficientSource, realDensityMeasure_apply volume _ hi
      (fun r => (smoothProductProfile_range I r).1) (measurableSet_lt measurable_const measurable_norm)]
    have hz : (∫ r in {r : I → ℝ | 1 < ‖r‖}, smoothProductProfile I r) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun r hr => smoothProductProfile_zero_outside I r hr
    rw [hz, ENNReal.ofReal_zero]
  exact (ae_iff.mpr (by simpa only [not_le] using hnull))

theorem unitCoefficientSource_affine_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (unitCoefficientSource I).map (fun r i => c i+w i*r i) =
      realDensityMeasure volume (affineProductProfile c w) :=
  affineProductProfile_law c w hw

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

theorem unitCoefficientSource_pi (I : Type*) [Fintype I] :
    unitCoefficientSource I = Measure.pi (fun _ : I => realDensityMeasure volume smoothProbabilityProfile) := by
  symm
  exact realDensityMeasure_pi (fun _ => volume) (fun _ => smoothProbabilityProfile)
    (fun _ => smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport
      smoothProbabilityProfile_compact) (fun _ r => (smoothProbabilityProfile_range r).1)

theorem unitCoefficientSource_reindex {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    (unitCoefficientSource I).map (fun r => r ∘ e.symm) = unitCoefficientSource J := by
  let : IsProbabilityMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_probability volume _
      (smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport
        smoothProbabilityProfile_compact)
      (fun r => (smoothProbabilityProfile_range r).1) smoothProbabilityProfile_integral
  rw [unitCoefficientSource_pi, unitCoefficientSource_pi]
  have he : (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e : (I → ℝ) → J → ℝ) =
      fun r => r ∘ e.symm := by
    funext r j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [← he]
  exact Measure.pi_map_piCongrLeft e (fun _ => realDensityMeasure volume smoothProbabilityProfile)

theorem affineCoefficientProduct_unit_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    (unitCoefficientSource I).map (fun r j => c j+w j*r (e.symm j)) =
      Measure.pi (fun j => affineCoefficientMeasure (c j) (w j)) := by
  have hm : Measurable (fun r : J → ℝ => fun j => c j+w j*r j) := by fun_prop
  have he : Measurable (fun r : I → ℝ => r ∘ e.symm) := by fun_prop
  change (unitCoefficientSource I).map
    ((fun r : J → ℝ => fun j => c j+w j*r j) ∘ (fun r => r ∘ e.symm)) = _
  rw [← Measure.map_map hm he, unitCoefficientSource_reindex,
    unitCoefficientSource_affine_law c w hw, affineCoefficientProduct_density c w hw]

theorem normalizedIntegerColumns_one_mulVec {O J : Type*}
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (A : Matrix O J ℤ) (S v : J → ℝ) :
    A.map (Int.cast : ℤ → ℝ) *ᵥ (fun j => S j*v j) =
      normalizedIntegerColumns A S (fun _ => 1) *ᵥ v := by
  ext i
  change (∑ j, (A i j : ℝ)*(S j*v j)) = ∑ j, normalizedIntegerColumns A S (fun _ => 1) i j*v j
  simp only [normalizedIntegerColumns_entry_div, div_one]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem affineCoefficientProduct_scaled_image {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O]
    (e : I ≃ J) (A : Matrix O J ℤ) (c w S : J → ℝ)
    (hw : ∀ j, 0 < w j) (hS : ∀ j, 0 < S j) :
    (Measure.pi (fun j => affineCoefficientMeasure (S j*c j) (S j*w j))).map
      (fun a => A.map (Int.cast : ℤ → ℝ) *ᵥ a) =
      (unitCoefficientSource I).map (fun r =>
        normalizedIntegerColumns (A.submatrix id e) (S ∘ e) (fun _ => 1) *ᵥ
          (fun i => c (e i)+w (e i)*r i)) := by
  have hsample : Measurable (fun r : I → ℝ => fun j => S j*c j+S j*w j*r (e.symm j)) := by fun_prop
  have hmatrix : Measurable (fun a => A.map (Int.cast : ℤ → ℝ) *ᵥ a) :=
    (matrixSupCLM _).continuous.measurable
  rw [← affineCoefficientProduct_unit_reindex e _ _ (fun j => mul_pos (hS j) (hw j)),
    Measure.map_map hmatrix hsample]
  congr 1
  funext r
  let v : I → ℝ := fun i => S (e i)*(c (e i)+w (e i)*r i)
  have hv : (fun j => S j*c j+S j*w j*r (e.symm j)) = v ∘ e.symm := by
    funext j
    simp only [v, Function.comp_apply, e.apply_symm_apply]
    ring
  change A.map (Int.cast : ℤ → ℝ) *ᵥ (fun j => S j*c j+S j*w j*r (e.symm j)) = _
  have hr := Matrix.submatrix_mulVec_equiv (A.map (Int.cast : ℤ → ℝ)) v id e
  simp only [Function.comp_id] at hr
  rw [hv, ← hr]
  exact normalizedIntegerColumns_one_mulVec (A.submatrix id e) (S ∘ e) _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem unitCoefficientProjection_measurable {I J : Type*} (e : I → J) :
    Measurable (fun r : J → ℝ => r ∘ e) :=
  Measurable.of_eval (fun index => measurable_pi_apply (e index))

theorem unitCoefficientSource_marginal {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) :
    (unitCoefficientSource J).map (fun r => r ∘ e) = unitCoefficientSource I := by
  let ν : Measure ℝ := realDensityMeasure volume smoothProbabilityProfile
  have : IsProbabilityMeasure ν :=
    realDensityMeasure_probability volume _
      (smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport
        smoothProbabilityProfile_compact)
      (fun r => (smoothProbabilityProfile_range r).1) smoothProbabilityProfile_integral
  rw [unitCoefficientSource_pi, unitCoefficientSource_pi]
  change (Measure.pi (fun _ : J => ν)).map (fun r => r ∘ e) =
    Measure.pi (fun _ : I => ν)
  have hind : iIndepFun (fun j : J => fun r : J → ℝ => r j)
      (Measure.pi (fun _ : J => ν)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have he := hind.precomp e.injective
  have hm := he.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)
  change (Measure.pi (fun _ : J => ν)).map (fun r => r ∘ e) = _ at hm
  rw [hm]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : J => ν) (e i)).map_eq

theorem unitCoefficientSource_marginal_preserving {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) :
    MeasurePreserving (fun r : J → ℝ => r ∘ e)
      (unitCoefficientSource J) (unitCoefficientSource I) :=
  ⟨unitCoefficientProjection_measurable e, unitCoefficientSource_marginal e⟩

end Erdos3

end

end OAI
