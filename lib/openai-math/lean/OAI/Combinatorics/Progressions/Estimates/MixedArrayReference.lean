/-
Modified for ProveIt: use the older unconditional Measure.map_smul theorem
on Lean 4.32. Mathematical statements are unchanged.
-/
import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.Progressions.Geometry.ProductChartReference
import OAI.Combinatorics.Progressions.Probability.OrthonormalMixedLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

theorem pi_count_measure {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) =
      (Measure.count : Measure (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

theorem uniformPMF_toMeasure_pi {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    (PMF.uniformOfFintype (∀ i, X i)).toMeasure =
      Measure.pi (fun i => (PMF.uniformOfFintype (X i)).toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  rw [(PMF.uniformOfFintype (∀ i, X i)).toMeasure_apply_singleton x (measurableSet_singleton x),
    Measure.pi_singleton]
  have he (i) : (PMF.uniformOfFintype (X i)).toMeasure {x i} =
      (Fintype.card (X i) : ℝ≥0∞)⁻¹ := by
    rw [(PMF.uniformOfFintype (X i)).toMeasure_apply_singleton (x i) (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
  simp only [he, PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))

theorem pi_smul_finite {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (c : I → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  let : ∀ i, SigmaFinite (c i • μ i) := fun i => ennreal_smul_sigmaFinite (μ i) (c i) (hc i)
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

def mixedArrayRegroup (I Z J : Type*) :
    ((I → J → ℝ) × (Z → J → ℤ)) ≃ᵐ (J → (I → ℝ) × (Z → ℤ)) :=
  ((finiteArrayTranspose I J ℝ).prodCongr (finiteArrayTranspose Z J ℤ)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J).symm

theorem mixedArrayRegroup_apply {I Z J : Type*} (x : (I → J → ℝ) × (Z → J → ℤ)) (j : J) :
    mixedArrayRegroup I Z J x j = (fun i => x.1 i j, fun z => x.2 z j) := rfl

theorem mixedArrayRegroup_measurePreserving {I Z J : Type*}
    [Fintype I] [Fintype Z] [Fintype J]
    (μ : I → J → Measure ℝ) (ν : Z → J → Measure ℤ)
    [∀ i j, SigmaFinite (μ i j)] [∀ z j, SigmaFinite (ν z j)] :
    MeasurePreserving (mixedArrayRegroup I Z J)
      ((Measure.pi (fun i => Measure.pi (μ i))).prod (Measure.pi (fun z => Measure.pi (ν z))))
      (Measure.pi (fun j => (Measure.pi (fun i => μ i j)).prod (Measure.pi (fun z => ν z j)))) := by
  have h₁ := (finiteArrayTranspose_measurePreserving μ).prod (finiteArrayTranspose_measurePreserving ν)
  have h₂ := (measurePreserving_arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J
    (fun j => Measure.pi (fun i => μ i j)) (fun j => Measure.pi (fun z => ν z j))).symm
      (MeasurableEquiv.arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J)
  exact h₂.comp h₁

noncomputable def mixedScalarArrayLaw {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) : Measure ((I → J → ℝ) × (Z → J → ℤ)) :=
  (Measure.pi (fun i => Measure.pi (fun j => affineCoefficientMeasure (c i j) (w i j)))).prod
    (Measure.pi (fun z => Measure.pi (fun j => (p z j).toMeasure)))

theorem mixedScalarArrayLaw_probability {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (mixedScalarArrayLaw c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  unfold mixedScalarArrayLaw
  infer_instance

theorem mixedScalarArrayLaw_regroup {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    Measure.map (mixedArrayRegroup I Z J) (mixedScalarArrayLaw c w p) =
      Measure.pi (fun j => mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun z => p z j)) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  exact (mixedArrayRegroup_measurePreserving (fun i j => affineCoefficientMeasure (c i j) (w i j))
    (fun z j => (p z j).toMeasure)).map_eq

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

noncomputable def mixedArrayReference (I Z O : Type*) [Fintype I] [Fintype O] :
    Measure ((I → O → ℝ) × (Z → O → ℤ)) :=
  (volume : Measure (I → O → ℝ)).prod (Measure.count : Measure (Z → O → ℤ))

instance mixedArrayReference_sigmaFinite (I Z O : Type*) [Fintype I] [Fintype Z] [Fintype O] :
    SigmaFinite (mixedArrayReference I Z O) := by
  unfold mixedArrayReference
  infer_instance

theorem mixedArrayRegroup_volume_count (I Z O : Type*) [Fintype I] [Fintype Z] [Fintype O] :
    MeasurePreserving (mixedArrayRegroup I Z O) (mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => (volume : Measure (I → ℝ)).prod (Measure.count : Measure (Z → ℤ)))) := by
  simpa only [mixedArrayReference, volume_pi, pi_count_measure] using
    (mixedArrayRegroup_measurePreserving (fun _ : I => fun _ : O => (volume : Measure ℝ))
      (fun _ : Z => fun _ : O => (Measure.count : Measure ℤ)))

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

noncomputable def orthonormalArrayChart :
    ((I → O → ℝ) × (Z → O → ℤ)) ≃ᵐ (O → E × (Z → ℤ)) :=
  (mixedArrayRegroup I Z O).trans
    (MeasurableEquiv.piCongrRight (fun _ : O => orthonormalMixedChart (J := Z) o))

omit [FiniteDimensional ℝ E] [Fintype Z] in
theorem orthonormalArrayChart_apply (x : (I → O → ℝ) × (Z → O → ℤ)) (t : O) :
    orthonormalArrayChart o x t = orthonormalMixedChart o (mixedArrayRegroup I Z O x t) := rfl

variable [Fintype O]

theorem orthonormalArrayChart_measurePreserving :
    MeasurePreserving (orthonormalArrayChart (O := O) (Z := Z) o) (mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))) := by
  have h := measurePreserving_pi
    (fun _ : O => (volume : Measure (I → ℝ)).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ : O => (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ => orthonormalMixedChart_measurePreserving (J := Z) o)
  exact h.comp (mixedArrayRegroup_volume_count I Z O)

theorem orthonormalArrayChart_scaled_reference (c : ℝ≥0∞) (hc : c ≠ ∞) :
    MeasurePreserving (orthonormalArrayChart (O := O) (Z := Z) o)
      (c ^ Fintype.card O • mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))) := by
  refine ⟨(orthonormalArrayChart o).measurable, ?_⟩
  rw [Measure.map_smul,
    (orthonormalArrayChart_measurePreserving o).map_eq,
    pi_smul_finite _ _ (fun _ => hc)]
  simp only [Finset.prod_const, Finset.card_univ]

noncomputable def arrayResidueChart {R : Type*} [MeasurableSpace R] :
    (((I → O → ℝ) × (Z → O → ℤ)) × (O → R)) ≃ᵐ (O → (E × (Z → ℤ)) × R) :=
  ((orthonormalArrayChart o).prodCongr (MeasurableEquiv.refl _)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (E × (Z → ℤ)) R O).symm

theorem arrayResidueChart_measurePreserving {R : Type*} [MeasurableSpace R]
    (ν : Measure R) [SigmaFinite ν] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    MeasurePreserving (arrayResidueChart (O := O) (Z := Z) o)
      ((c ^ Fintype.card O • mixedArrayReference I Z O).prod (Measure.pi (fun _ : O => ν)))
      (Measure.pi (fun _ : O => (c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ))).prod ν)) := by
  let : SigmaFinite (c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ))) :=
    ennreal_smul_sigmaFinite _ c hc
  have h₁ := (orthonormalArrayChart_scaled_reference (O := O) (Z := Z) o c hc).prod
    (MeasurePreserving.id (Measure.pi (fun _ : O => ν)))
  have h₂ := (measurePreserving_arrowProdEquivProdArrow (E × (Z → ℤ)) R O
    (fun _ => c • (volume : Measure E).prod (Measure.count : Measure (Z → ℤ)))
    (fun _ => ν)).symm (MeasurableEquiv.arrowProdEquivProdArrow (E × (Z → ℤ)) R O)
  exact h₂.comp h₁

end Erdos3

end

end OAI
