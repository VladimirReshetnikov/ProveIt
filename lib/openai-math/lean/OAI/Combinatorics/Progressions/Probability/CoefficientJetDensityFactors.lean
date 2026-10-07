/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.JointMixedCoefficientComparison
import OAI.Combinatorics.Progressions.Geometry.JetAxisCoordinates
import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid
import OAI.Combinatorics.Progressions.Sampling.CoveredJetSampler

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {I Z O J : Type*} [Fintype I] [Fintype Z]
variable [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
variable (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)

noncomputable def integerMatrixImagePMF (p : J → PMF ℤ) : PMF (O → ℤ) :=
  (independentProductPMF p).map (fun z => A *ᵥ z)

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
theorem integerMatrixImagePMF_law (p : J → PMF ℤ) :
    (Measure.pi (fun j => (p j).toMeasure)).map (fun z => A *ᵥ z) =
      (integerMatrixImagePMF A p).toMeasure := by
  rw [integerMatrixImagePMF, ← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  congr 1
  exact (Measure.toPMF_toMeasure _).symm

noncomputable def mixedArrayImageDensity (c w : I → J → ℝ) (p : Z → J → PMF ℤ)
    (x : (I → O → ℝ) × (Z → O → ℤ)) : ℝ :=
  (∏ i, integerMatrixRealDensity A s hA (affineProductProfile (c i) (w i)) (x.1 i)) *
    ∏ z, (integerMatrixImagePMF A (p z) (x.2 z)).toReal

theorem mixedArrayImageDensity_measurable (c w : I → J → ℝ) (p : Z → J → PMF ℤ) :
    Measurable (mixedArrayImageDensity A s hA c w p) := by
  apply Measurable.mul
  · exact Finset.measurable_prod _ (fun i _ =>
      (integerMatrixRealDensity_measurable A s hA
        (affineProductProfile_contDiff (c i) (w i)).continuous.measurable).comp
          ((measurable_pi_apply i).comp measurable_fst))
  · exact (measurable_of_countable (fun x : Z → O → ℤ =>
      ∏ z, (integerMatrixImagePMF A (p z) (x z)).toReal)).comp measurable_snd

theorem mixedArrayImageDensity_nonneg (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (p : Z → J → PMF ℤ) (x : (I → O → ℝ) × (Z → O → ℤ)) :
    0 ≤ mixedArrayImageDensity A s hA c w p x :=
  mul_nonneg (Finset.prod_nonneg (fun i _ => integerMatrixRealDensity_nonneg A s hA
    (affineProductProfile_nonneg (c i) (w i) (hw i)) _))
      (Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem mixedArrayImageDensity_integrable (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (p : Z → J → PMF ℤ) :
    Integrable (mixedArrayImageDensity A s hA c w p) (mixedArrayReference I Z O) := by
  have hr := Integrable.fintype_prod_dep (fun i => integerMatrixRealDensity_integrable A s hA
    (affineProductProfile_integrable (c i) (w i) (hw i)))
  have hz := Integrable.fintype_prod_dep (fun z => pmf_real_integrable (integerMatrixImagePMF A (p z)))
  rw [pi_count_measure] at hz
  exact hr.mul_prod hz

theorem mixedArrayImageDensity_law (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (p : Z → J → PMF ℤ) :
    (mixedScalarArrayLaw c w p).map (mixedArrayIntegerImage A) =
      realDensityMeasure (mixedArrayReference I Z O) (mixedArrayImageDensity A s hA c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  have hR : Measurable (fun x : J → ℝ => A.map (Int.cast : ℤ → ℝ) *ᵥ x) :=
    (matrixSupCLM _).continuous.measurable
  have hZ : Measurable (fun z : J → ℤ => A *ᵥ z) := measurable_of_countable _
  have hr : (Measure.pi (fun i => Measure.pi (fun j =>
        affineCoefficientMeasure (c i j) (w i j)))).map
      (fun x i => A.map (Int.cast : ℤ → ℝ) *ᵥ x i) =
      realDensityMeasure volume (fun x : I → O → ℝ =>
        ∏ i, integerMatrixRealDensity A s hA (affineProductProfile (c i) (w i)) (x i)) := by
    rw [Measure.pi_map_pi (fun _ => hR.aemeasurable)]
    simp_rw [integerMatrixRealDensity_affine_law A s hA _ _ (hw _)]
    exact realDensityMeasure_pi (fun _ => volume) _
      (fun i => integerMatrixRealDensity_integrable A s hA
        (affineProductProfile_integrable (c i) (w i) (hw i)))
      (fun i => integerMatrixRealDensity_nonneg A s hA
        (affineProductProfile_nonneg (c i) (w i) (hw i)))
  have hz : (Measure.pi (fun z => Measure.pi (fun j => (p z j).toMeasure))).map
      (fun x z => A *ᵥ x z) =
      realDensityMeasure Measure.count (fun x : Z → O → ℤ =>
        ∏ z, (integerMatrixImagePMF A (p z) (x z)).toReal) := by
    rw [Measure.pi_map_pi (fun _ => hZ.aemeasurable)]
    simp_rw [integerMatrixImagePMF_law, pmf_realDensity_count]
    rw [realDensityMeasure_pi _ _ (fun z => pmf_real_integrable (integerMatrixImagePMF A (p z)))
      (fun _ _ => ENNReal.toReal_nonneg), pi_count_measure]
    rfl
  change ((Measure.pi (fun i => Measure.pi (fun j => affineCoefficientMeasure (c i j) (w i j)))).prod
    (Measure.pi (fun z => Measure.pi (fun j => (p z j).toMeasure)))).map
      (Prod.map (fun x i => A.map (Int.cast : ℤ → ℝ) *ᵥ x i) (fun x z => A *ᵥ x z)) = _
  have hRa : Measurable (fun x : I → J → ℝ => fun i => A.map (Int.cast : ℤ → ℝ) *ᵥ x i) :=
    Measurable.of_eval (fun index => hR.comp (measurable_pi_apply index))
  have hZa : Measurable (fun x : Z → J → ℤ => fun z => A *ᵥ x z) :=
    Measurable.of_eval (fun index => hZ.comp (measurable_pi_apply index))
  rw [← Measure.map_prod_map _ _ hRa hZa, hr, hz]
  apply binaryDensity_measure
  · exact Finset.measurable_prod _ (fun i _ =>
      (integerMatrixRealDensity_measurable A s hA
        (affineProductProfile_contDiff (c i) (w i)).continuous.measurable).comp (measurable_pi_apply i))
  · exact measurable_of_countable _
  · intro x
    exact Finset.prod_nonneg (fun i _ => integerMatrixRealDensity_nonneg A s hA
      (affineProductProfile_nonneg (c i) (w i) (hw i)) _)

theorem mixedArrayImageDensity_probability (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (realDensityMeasure (mixedArrayReference I Z O)
      (mixedArrayImageDensity A s hA c w p)) := by
  let := mixedScalarArrayLaw_probability c w hw p
  rw [← mixedArrayImageDensity_law A s hA c w hw p]
  infer_instance

theorem mixedArrayImageDensity_mass (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (p : Z → J → PMF ℤ) :
    (∫ x, mixedArrayImageDensity A s hA c w p x ∂mixedArrayReference I Z O) = 1 := by
  let := mixedArrayImageDensity_probability A s hA c w hw p
  have h := realDensityMeasure_real_univ (mixedArrayReference I Z O)
    (mixedArrayImageDensity A s hA c w p) (mixedArrayImageDensity_integrable A s hA c w hw p)
    (mixedArrayImageDensity_nonneg A s hA c w hw p)
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one] using h.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {I Q : Type*} [Fintype I] [Fintype Q] {Y : I → Type*} {X : Q → Type*}
variable [∀ i, MeasurableSpace (Y i)] [∀ q, Countable (X q)]
variable [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSingletonClass (X q)]

noncomputable def jointMixedCoefficientDensity (g : ∀ i, Y i → ℝ) (p : ∀ q, PMF (X q))
    (v : (∀ i, Y i) × (∀ q, X q)) : ℝ :=
  (∏ i, g i (v.1 i)) * (dependentProductPMF p v.2).toReal

omit [∀ i, MeasurableSpace (Y i)] in
theorem jointMixedCoefficientDensity_expand (g : ∀ i, Y i → ℝ) (p : ∀ q, PMF (X q))
    (v : (∀ i, Y i) × (∀ q, X q)) :
    jointMixedCoefficientDensity g p v = (∏ i, g i (v.1 i)) * ∏ q, (p q (v.2 q)).toReal := by
  simp only [jointMixedCoefficientDensity, dependentProductPMF_apply, ENNReal.toReal_prod]

theorem jointMixedCoefficientDensity_measurable (g : ∀ i, Y i → ℝ)
    (p : ∀ q, PMF (X q)) (hg : ∀ i, Measurable (g i)) :
    Measurable (jointMixedCoefficientDensity g p) := by
  exact (Finset.measurable_prod _ (fun i _ =>
    (hg i).comp ((measurable_pi_apply i).comp measurable_fst))).mul
      ((measurable_of_countable (fun x => (dependentProductPMF p x).toReal)).comp measurable_snd)

omit [∀ i, MeasurableSpace (Y i)] in
theorem jointMixedCoefficientDensity_nonneg (g : ∀ i, Y i → ℝ)
    (p : ∀ q, PMF (X q)) (hg : ∀ i y, 0 ≤ g i y) (v : (∀ i, Y i) × (∀ q, X q)) :
    0 ≤ jointMixedCoefficientDensity g p v :=
  mul_nonneg (Finset.prod_nonneg (fun i _ => hg i _)) ENNReal.toReal_nonneg

theorem jointMixedCoefficientDensity_integrable (ν : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (ν i)]
    (g : ∀ i, Y i → ℝ) (p : ∀ q, PMF (X q)) (hg : ∀ i, Integrable (g i) (ν i)) :
    Integrable (jointMixedCoefficientDensity g p) ((Measure.pi ν).prod Measure.count) :=
  (Integrable.fintype_prod_dep hg).mul_prod (pmf_real_integrable (dependentProductPMF p))

theorem jointMixedCoefficientDensity_law (ν : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (ν i)]
    (g : ∀ i, Y i → ℝ) (p : ∀ q, PMF (X q))
    (hgm : ∀ i, Measurable (g i)) (hgi : ∀ i, Integrable (g i) (ν i))
    (hg0 : ∀ i y, 0 ≤ g i y) :
    (Measure.pi (fun i => realDensityMeasure (ν i) (g i))).prod
      (Measure.pi (fun q => (p q).toMeasure)) =
        realDensityMeasure ((Measure.pi ν).prod Measure.count) (jointMixedCoefficientDensity g p) := by
  have hp : Measure.pi (fun q => (p q).toMeasure) = (dependentProductPMF p).toMeasure := by
    exact (Measure.toPMF_toMeasure _).symm
  rw [realDensityMeasure_pi ν g hgi hg0, hp, pmf_realDensity_count]
  exact binaryDensity_measure _ _ _ _
    (Finset.measurable_prod _ (fun i _ => (hgm i).comp (measurable_pi_apply i)))
    (measurable_of_countable _) (fun y => Finset.prod_nonneg (fun i _ => hg0 i (y i)))

omit [∀ i, MeasurableSpace (Y i)] in
theorem jointMixedCoefficientDensity_scaled (g : ∀ i, Y i → ℝ) (p : ∀ q, PMF (X q))
    (S : Q → ℝ) (v : (∀ i, Y i) × (∀ q, X q)) :
    (∏ q, S q) * jointMixedCoefficientDensity g p v =
      (∏ i, g i (v.1 i)) * ∏ q, S q*(p q (v.2 q)).toReal := by
  rw [jointMixedCoefficientDensity, mul_left_comm, dependentProductPMF_scaled]

theorem jointMixedCoefficientDensity_test_mean {Ω : Type*} [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (ν : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (ν i)]
    (g : Ω → ∀ i, Y i → ℝ) (p : Ω → ∀ q, PMF (X q))
    (hgm : ∀ ω i, Measurable (g ω i)) (hgi : ∀ ω i, Integrable (g ω i) (ν i))
    (hg0 : ∀ ω i y, 0 ≤ g ω i y)
    (φ : (∀ i, Y i) × (∀ q, X q) → ℂ) (hφ : Measurable φ)
    {B : ℝ} (hbound : ∀ v, ‖φ v‖ ≤ B) :
    outer.complexMean (fun ω => ∫ v, φ v ∂
      (Measure.pi (fun i => realDensityMeasure (ν i) (g ω i))).prod
        (Measure.pi (fun q => (p ω q).toMeasure))) =
      ∫ v, (outer.mean (fun ω => jointMixedCoefficientDensity (g ω) (p ω) v) : ℂ) * φ v
        ∂(Measure.pi ν).prod Measure.count := by
  simp_rw [jointMixedCoefficientDensity_law ν _ _ (hgm _) (hgi _) (hg0 _),
    realDensityMeasure_integral_complex _ _ (jointMixedCoefficientDensity_measurable _ _ (hgm _))
      (jointMixedCoefficientDensity_nonneg _ _ (hg0 _))]
  have hi (ω) : Integrable (fun v => (jointMixedCoefficientDensity (g ω) (p ω) v : ℂ) * φ v)
      ((Measure.pi ν).prod Measure.count) :=
    (jointMixedCoefficientDensity_integrable ν _ _ (hgi ω)).ofReal.mul_bdd
      hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [← outer.integral_complexMean _ _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => outer.complexMean_ofReal_mul _ (φ v))

theorem mixedArrayImageDensity_eq_jointMixed {J O : Type*}
    [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (c w : I → J → ℝ) (p : Q → J → PMF ℤ)
    (v : (I → O → ℝ) × (Q → O → ℤ)) :
    mixedArrayImageDensity A s hA c w p v =
      jointMixedCoefficientDensity
        (fun i => integerMatrixRealDensity A s hA (affineProductProfile (c i) (w i)))
        (fun q => integerMatrixImagePMF A (p q)) v := by
  rw [jointMixedCoefficientDensity_expand]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem coefficientPMF_smooth_eq {J : Type*} [Fintype J]
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → smoothProductProfile J x = 0)
    (hZ : 0 < coefficientWeightSum (smoothProductProfile J) S) :
    coefficientPMF (smoothProductProfile J) (fun x => (smoothProductProfile_range J x).1)
      S hS hs hZ = smoothProductPMF S hS := rfl

theorem coefficientImagePMF_smooth_eq {O J : Type*} [Fintype J]
    (A : Matrix O J ℤ) (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → smoothProductProfile J x = 0)
    (hZ : 0 < coefficientWeightSum (smoothProductProfile J) S) :
    coefficientImagePMF A (smoothProductProfile J) (fun x => (smoothProductProfile_range J x).1)
      S hS hs hZ = smoothMatrixImagePMF A S hS := rfl

theorem integerMatrixImagePMF_smooth_eq {O J : Type*} [Fintype J]
    (A : Matrix O J ℤ) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    integerMatrixImagePMF A (fun j => smoothCoefficientPMF (S j) (hS j)) =
      smoothMatrixImagePMF A S hS := by
  unfold integerMatrixImagePMF smoothMatrixImagePMF
  congr 1
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [independentProductPMF_toReal, smoothProductPMF_apply]

theorem coefficientImagePMF_affine_eq {O J : Type*} [Fintype J]
    (A : Matrix O J ℤ) (c w S : J → ℝ) (hw : ∀ j, 0 < w j) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hs : ∀ x, R < ‖x‖ → affineProductProfile c w x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) :
    coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
      S hS hs hZ = integerMatrixImagePMF A (fun j =>
        shiftedSmoothCoefficientPMF (c j * S j) (w j * S j) (mul_pos (hw j) (hS j))
          (affineProfile_coordinate_sum_pos c w S hw hS hZ j)) := by
  unfold coefficientImagePMF integerMatrixImagePMF
  congr 1
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [affineCoefficientPMF_apply c w S hw hS hs hZ, independentProductPMF_toReal]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical Matrix

theorem pmf_map_injective_comp_apply {X Y Z : Type*} (p : PMF X)
    (f : X → Y) (g : Y → Z) (hg : Function.Injective g) (y : Y) :
    p.map (g ∘ f) (g y) = p.map f y := by
  simp only [PMF.map_apply, Function.comp_apply, hg.eq_iff]

theorem integerMatrixImagePMF_reindex_rows {O O' K : Type*} [Fintype K]
    (e : O' ≃ O) (A : Matrix O K ℤ) (p : K → PMF ℤ) (z : O → ℤ) :
    integerMatrixImagePMF (A.submatrix e id) p (z ∘ e) = integerMatrixImagePMF A p z := by
  exact pmf_map_injective_comp_apply (independentProductPMF p) (fun c => A *ᵥ c)
    (fun v => v ∘ e) (fun _ _ h => funext (fun i => by
      obtain ⟨i, rfl⟩ := e.surjective i
      exact congrFun h i)) z

namespace VectorPolynomial
variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O O' B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)] [∀ j, Fintype (B j)]

theorem coefficientDeckJetDensity_reindex_rows (e : ∀ j, O' j ≃ O j)
    (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d : ℕ) [NeZero d] (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root A (fun j => rows j ∘ e j) d (fun j t => r j (e j t)) =
      coefficientDeckJetDensity root A rows d r := by
  let E : (∀ j, O j → B j → ZMod d) ≃ (∀ j, O' j → B j → ZMod d) :=
    Equiv.piCongrRight (fun j => (Equiv.piCongrLeft (fun _ : O j => B j → ZMod d) (e j)).symm)
  have hc : Fintype.card (∀ j, O' j → B j → ZMod d) =
      Fintype.card (∀ j, O j → B j → ZMod d) := Fintype.card_congr E.symm
  unfold coefficientDeckJetDensity
  rw [hc]
  congr 2
  exact pmf_map_injective_comp_apply _ (coefficientDeckJetMap root A rows d) E E.injective r

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O I : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]
variable [∀ j, DecidableEq (O j)]
variable {n : Fin m → ℕ} (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (pivot : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
  id (pivot j)).det ≠ 0)

noncomputable def canonicalCoefficientJetImageDensity
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (x : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : ℝ :=
  ∏ j, mixedArrayImageDensity (I := I j) (Z := Fin (n j)) (O := O j)
    (J := BoundedCoefficientExponent K (j.val + 1))
    (boundedCoefficientJetMatrix root A (j.val + 1) (rows j))
    (pivot j) (hpivot j) (c j) (w j) (p j) (x j)

theorem canonicalCoefficientJetImageDensity_measurable
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ) :
    Measurable (canonicalCoefficientJetImageDensity root A rows pivot hpivot c w p) :=
  Finset.measurable_prod _ (fun j _ => (mixedArrayImageDensity_measurable _
    (pivot j) (hpivot j) (c j) (w j) (p j)).comp (measurable_pi_apply j))

theorem canonicalCoefficientJetImageDensity_nonneg
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (hw : ∀ j i e, 0 < w j i e)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ) (x) :
    0 ≤ canonicalCoefficientJetImageDensity root A rows pivot hpivot c w p x :=
  Finset.prod_nonneg (fun j _ => mixedArrayImageDensity_nonneg _
    (pivot j) (hpivot j) (c j) (w j) (hw j) (p j) (x j))

theorem canonicalCoefficientJetImageDensity_integrable
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (hw : ∀ j i e, 0 < w j i e)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ) :
    Integrable (canonicalCoefficientJetImageDensity root A rows pivot hpivot c w p)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))) :=
  Integrable.fintype_prod_dep (fun j => mixedArrayImageDensity_integrable _
    (pivot j) (hpivot j) (c j) (w j) (hw j) (p j))

theorem canonicalCoefficientJetImageDensity_law
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (hw : ∀ j i e, 0 < w j i e)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ) :
    (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).map
      (canonicalCoefficientJetArrays root A rows) =
    realDensityMeasure (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      (canonicalCoefficientJetImageDensity root A rows pivot hpivot c w p) := by
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (c j) (w j) (p j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  unfold canonicalCoefficientJetArrays
  rw [Measure.pi_map_pi (fun j => (mixedArrayIntegerImage_measurable
    (boundedCoefficientJetMatrix root A (j.val + 1) (rows j))).aemeasurable)]
  simp_rw [mixedArrayImageDensity_law _ (pivot _) (hpivot _) _ _ (hw _) _]
  exact realDensityMeasure_pi _ _
    (fun j => mixedArrayImageDensity_integrable _ (pivot j) (hpivot j) (c j) (w j) (hw j) (p j))
    (fun j => mixedArrayImageDensity_nonneg _ (pivot j) (hpivot j) (c j) (w j) (hw j) (p j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K : Type*} [Fintype K] {m : ℕ}
variable {I O : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (O j)]
variable [∀ j, DecidableEq (O j)] {n : Fin m → ℕ}
variable (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val + 1)) ℤ)
variable (s : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hA : ∀ j, ((A j).submatrix id (s j)).det ≠ 0)
variable (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def coefficientJetDensityFactor :
    ∀ a : LayerSamplerAxis I n, CoefficientJetAxisRow O a → ℝ
  | ⟨j, .inl i⟩ => integerMatrixRealDensity (A j) (s j) (hA j) (affineProductProfile (c j i) (w j i))
  | ⟨j, .inr i⟩ => fun z => (integerMatrixImagePMF (A j) (p j i) z).toReal

theorem canonicalCoefficientJetImageDensity_axis_product
    {α : Type*} [DecidableEq α] (root : K → ℤ) (dirs : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α)
    (hp : ∀ j, ((boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    canonicalCoefficientJetImageDensity root dirs rows s hp c w p z =
      ∏ a, coefficientJetDensityFactor
        (fun j => boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)) s hp c w p a
          (coefficientJetAxisEquiv O I n z a) := by
  simp only [canonicalCoefficientJetImageDensity, Fintype.prod_sigma, Fintype.prod_sum_type,
    coefficientJetDensityFactor, coefficientJetAxisEquiv_real, coefficientJetAxisEquiv_integer]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
