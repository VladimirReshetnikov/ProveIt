/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
import OAI.Combinatorics.Progressions.Sampling.JointFrozenSamplerLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

abbrev AllocatedLongJetRows (O : Fin m → Type*) :=
  ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val

noncomputable def allocatedLongJetReference (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    Measure (AllocatedLongJetRows B U basis S O) :=
  Measure.pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)

instance allocatedLongJetReference_sigmaFinite (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    SigmaFinite (allocatedLongJetReference B U basis S O) := by
  unfold allocatedLongJetReference
  infer_instance

variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

noncomputable def allocatedLongJetMap (c : AllocatedLongCoefficients B U basis S) :
    AllocatedLongJetRows B U basis S O :=
  fun a => coefficientJetAxisMap (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val (c a)

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetMap_measurable : Measurable (allocatedLongJetMap B U basis S x u v rows) :=
  Measurable.of_eval (fun a =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val).comp
      (measurable_pi_apply a))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetMap_reconstruct (c₀ : AllocatedFrozenCoefficients B U basis S)
    (c₁ : AllocatedLongCoefficients B U basis S) (a : {a // ¬grid a}) :
    coefficientJetAxisMap (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val
      (coefficientAxisEquiv (LayerSamplerVariables G I n B) I n
        ((allocatedCoefficientSplit B U basis S).symm (c₀, c₁)) a.val) =
      allocatedLongJetMap B U basis S x u v rows c₁ a := by
  rw [allocatedCoefficientReconstruct_long]
  rfl

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

noncomputable def allocatedLongJetFactor :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ =>
      allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
        (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
  | ⟨⟨j, .inr i⟩, ha⟩ =>
      fun z => (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j)
        (Nat.lt_of_not_ge ha) z).toReal

theorem allocatedLongJetFactor_law (a : {a // ¬grid a}) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S a.val).map
      (coefficientJetAxisMap (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val) =
      realDensityMeasure (coefficientJetAxisReference O a.val)
        (allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact allocatedContinuousKernel_image_law B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j) v
  | inr i =>
    change (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map
      (fun c => allocatedPartitionedJetMatrix B U basis S x u v rows j *ᵥ c) =
      realDensityMeasure Measure.count (fun z =>
        (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha) z).toReal)
    rw [← pmf_realDensity_count]
    exact allocatedIntegerKernelPMF_law B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha)

theorem allocatedLongJetFactor_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change Measurable (allocatedContinuousKernelDensity B U basis S j i x u
      (rows j) (s j) (hA j) (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v))
    exact (allocatedContinuousKernelDensity_measurable B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j)).of_uncurry_left
  | inr i =>
    change Measurable (fun z : O j → ℤ =>
      (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha) z).toReal)
    exact measurable_of_countable _

theorem allocatedLongJetFactor_probability_data (a : {a // ¬grid a}) :
    (∀ z, 0 ≤ allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z) ∧
      Integrable (allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a)
        (coefficientJetAxisReference O a.val) ∧
      (∫ z, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z
        ∂coefficientJetAxisReference O a.val) = 1 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact allocatedContinuousKernelDensity_probability_data B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j)
      (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
  | inr i =>
    let p := allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha)
    change (∀ z, 0 ≤ (p z).toReal) ∧ Integrable (fun z => (p z).toReal) Measure.count ∧
      (∫ z, (p z).toReal ∂Measure.count) = 1
    exact ⟨fun _ => ENNReal.toReal_nonneg, pmf_real_integrable p, pmf_real_integral_count p⟩

noncomputable def allocatedLongJetDensity (z : AllocatedLongJetRows B U basis S O) : ℝ :=
  ∏ a, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a)

theorem allocatedLongJetDensity_measurable :
    Measurable (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1) :=
  Finset.measurable_prod _ (fun a _ =>
    (allocatedLongJetFactor_measurable B U basis hR hσ S x u v rows s hA hσ1 a).comp (measurable_pi_apply a))

theorem allocatedLongJetDensity_probability_data :
    (∀ z, 0 ≤ allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) ∧
      Integrable (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1)
        (allocatedLongJetReference B U basis S O) ∧
      (∫ z, allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z
        ∂allocatedLongJetReference B U basis S O) = 1 := by
  have hp := allocatedLongJetFactor_probability_data B U basis hR hσ S x u v rows s hA hσ1
  refine ⟨fun z => Finset.prod_nonneg (fun a _ => (hp a).1 (z a)),
    Integrable.fintype_prod_dep (fun a => (hp a).2.1), ?_⟩
  change (∫ z, (∏ a, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a))
    ∂Measure.pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun a _ => (hp a).2.2)

theorem allocatedLongJetDensity_law :
    (allocatedLongCoefficientSource B U basis hR hσ S).map
      (allocatedLongJetMap B U basis S x u v rows) =
      realDensityMeasure (allocatedLongJetReference B U basis S O)
        (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1) := by
  let : ∀ a : {a // ¬grid a}, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a.val) :=
    fun a => allocatedCoefficientAxisLaw_probability B U basis hR hσ S a.val
  unfold allocatedLongCoefficientSource allocatedLongJetMap
  rw [Measure.pi_map_pi (fun a =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val).aemeasurable)]
  simp_rw [allocatedLongJetFactor_law B U basis hR hσ S x u v rows s hA hσ1]
  exact realDensityMeasure_pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val) _
    (fun a => (allocatedLongJetFactor_probability_data B U basis hR hσ S x u v rows s hA hσ1 a).2.1)
    (fun a => (allocatedLongJetFactor_probability_data B U basis hR hσ S x u v rows s hA hσ1 a).1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "source" => allocatedLongCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S O

theorem allocatedLongJet_test_integral
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ) :
    (∫ c, φ (allocatedLongJetMap B U basis S x u v rows c) ∂source) =
      ∫ z, (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z : ℂ) * φ z ∂reference := by
  rw [← integral_map (allocatedLongJetMap_measurable B U basis S x u v rows).aemeasurable hφ.aestronglyMeasurable,
    allocatedLongJetDensity_law B U basis hR hσ S x u v rows s hA hσ1,
    realDensityMeasure_integral_complex _ _
      (allocatedLongJetDensity_measurable B U basis hR hσ S x u v rows s hA hσ1)
      (allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).1]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

theorem allocatedLongJet_variable_test_mean
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides → AllocatedLongJetRows B U basis S O → ℂ)
    (hφ : ∀ v, Measurable (φ v)) {C : ℝ} (hbound : ∀ v z, ‖φ v z‖ ≤ C) :
    (∫ c, w.complexMean (fun v => φ v (allocatedLongJetMap B U basis S x u v rows c)) ∂source) =
      ∫ z, w.complexMean (fun v =>
        (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z : ℂ) * φ v z) ∂reference := by
  let : IsProbabilityMeasure source := allocatedLongCoefficientSource_probability B U basis hR hσ S
  have hi (v) : Integrable (fun c => φ v (allocatedLongJetMap B U basis S x u v rows c)) source :=
    (integrable_const C).mono'
      ((hφ v).comp (allocatedLongJetMap_measurable B U basis S x u v rows)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun c => hbound v _))
  rw [w.integral_complexMean _ _ hi]
  simp_rw [allocatedLongJet_test_integral B U basis hR hσ S x u rows s hA hσ1 _ _ (hφ _)]
  symm
  apply w.integral_complexMean
  intro v
  exact (allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1.ofReal.mul_bdd
    (hφ v).aestronglyMeasurable (Filter.Eventually.of_forall (hbound v))

theorem allocatedLongJet_test_mean
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ z, ‖φ z‖ ≤ C) :
    (∫ c, w.complexMean (fun v => φ (allocatedLongJetMap B U basis S x u v rows c)) ∂source) =
      ∫ z, (w.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) : ℂ) * φ z
        ∂reference := by
  rw [allocatedLongJet_variable_test_mean B U basis hR hσ S x u rows s hA hσ1 w
    (fun _ => φ) (fun _ => hφ) (fun _ => hbound)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => w.complexMean_ofReal_mul _ (φ z)))

end Erdos3.VectorPolynomial

end

end OAI
