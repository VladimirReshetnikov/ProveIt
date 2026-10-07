import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.Progressions.Probability.AllocatedWholeDeckLaw
import OAI.Combinatorics.Progressions.Sampling.AllocatedFrozenGridLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finitePMF_integral_measurable {X T : Type*} [MeasurableSpace X]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (p : PMF T) (f : X → T → ℂ) (hf : ∀ t, Measurable (fun x => f x t)) :
    Measurable (fun x => ∫ t, f x t ∂p.toMeasure) := by
  simp only [PMF.integral_eq_sum, Complex.real_smul]
  exact Finset.measurable_sum _ (fun t _ => (hf t).const_mul ((p t).toReal : ℂ))

theorem finitePMF_integral_norm_le {T : Type*} [MeasurableSpace T]
    (p : PMF T) (f : T → ℂ) {C : ℝ} (hf : ∀ t, ‖f t‖ ≤ C) :
    ‖∫ t, f t ∂p.toMeasure‖ ≤ C := by
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all p.toMeasure hf)

theorem finitePMF_integral_comp {T Y : Type*} [Fintype T] [Fintype Y]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : PMF T) (f : T → Y) (φ : Y → ℂ) :
    (∫ t, φ (f t) ∂p.toMeasure) = ∫ y, φ y ∂(p.map f).toMeasure := by
  rw [← PMF.toMeasure_map f p (measurable_of_finite f)]
  exact (integral_map (measurable_of_finite f).aemeasurable
    (measurable_of_finite φ).aestronglyMeasurable).symm

theorem probabilityProduct_finiteMean {X Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (w : FiniteProbabilityWeights T) (f : T → X × Y → ℂ)
    (hf : ∀ t, Measurable (f t)) {C : ℝ} (hb : ∀ t p, ‖f t p‖ ≤ C) :
    (∫ p, w.complexMean (fun t => f t p) ∂μ.prod ν) =
      ∫ x, w.complexMean (fun t => ∫ y, f t (x, y) ∂ν) ∂μ := by
  have hi (t) : Integrable (f t) (μ.prod ν) :=
    Integrable.of_bound (hf t).aestronglyMeasurable C (ae_of_all _ (hb t))
  rw [integral_prod _ (w.complexMean_integrable _ _ hi)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply w.integral_complexMean
  intro t
  exact Integrable.of_bound ((hf t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    C (ae_of_all _ (fun y => hb t (x, y)))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

theorem coefficientDeckJetDensity_integral
    (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d : ℕ) [NeZero d] (φ : (∀ j, O j → B j → ZMod d) → ℂ) :
    (∫ r, φ (coefficientDeckJetMap root A rows d r)
      ∂(PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
    ∫ r, (coefficientDeckJetDensity root A rows d r : ℂ) * φ r
      ∂(PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure := by
  rw [finitePMF_integral_comp _ (coefficientDeckJetMap root A rows d) φ,
    coefficientDeckJetDensity_law root A rows d,
    realDensityMeasure_integral_complex _ _ (measurable_of_finite _)
      (coefficientDeckJetDensity_nonneg root A rows d)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "join" => MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) grid
local notation "split" => allocatedCoefficientSplit B U b S
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

noncomputable def allocatedMixedJetReconstruct
    (a₀ : AllocatedFrozenCoefficients B U b S) (z : AllocatedLongJetRows B U b S O) :
    ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) :=
  (axis).symm ((join).symm (allocatedFrozenJetMap B U b S x u w rows a₀, z))

theorem allocatedMixedJetReconstruct_measurable [∀ j, Fintype (O j)] :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      allocatedMixedJetReconstruct B U b S x u w rows p.1 p.2) :=
  (axis).symm.measurable.comp ((join).symm.measurable.comp
    (((allocatedFrozenJetMap_measurable B U b S x u w rows).comp measurable_fst).prodMk measurable_snd))

theorem allocatedMixedJetReconstruct_physical
    (a₀ : AllocatedFrozenCoefficients B U b S) (a₁ : AllocatedLongCoefficients B U b S)
    (ha : AllocatedFrozenSupported B U b hR hσ S a₀) :
    allocatedMixedJetReconstruct B U b S x u w rows a₀
        (allocatedLongJetMap B U b S x u v rows a₁) =
      canonicalCoefficientJetArrays (root v) (dirs v) rows ((split).symm (a₀, a₁)) := by
  apply (axis).injective
  apply (join).injective
  simp only [allocatedMixedJetReconstruct, MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    change allocatedFrozenJetMap B U b S x u w rows a₀ i =
      axis (canonicalCoefficientJetArrays (root v) (dirs v) rows ((split).symm (a₀, a₁))) i.val
    rw [allocatedPhysicalJet_grid_reconstruct]
    exact congrFun (allocatedFrozenJetMap_eq_of_supported B U b hR hσ S x u w v rows a₀ ha) i
  · funext i
    change allocatedLongJetMap B U b S x u v rows a₁ i =
      allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm (a₀, a₁)) i
    exact congrFun (allocatedPhysicalLongJetMap_reconstruct B U b S x u v rows a₀ a₁).symm i

theorem allocatedMixedJetReconstruct_physical_split
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (ha : AllocatedFrozenSupported B U b hR hσ S (split a).1) :
    allocatedMixedJetReconstruct B U b S x u w rows (split a).1
        (allocatedPhysicalLongJetMap B U b S x u v rows a) =
      canonicalCoefficientJetArrays (root v) (dirs v) rows a := by
  rw [allocatedPhysicalLongJetMap_split]
  simpa only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
    allocatedMixedJetReconstruct_physical B U b hR hσ S x u v w rows (split a).1 (split a).2 ha

theorem allocatedCoefficientSource_frozen_supported :
    ∀ᵐ a ∂allocatedCoefficientSource B U b hR hσ S,
      AllocatedFrozenSupported B U b hR hσ S (split a).1 := by
  let : IsProbabilityMeasure (allocatedLongCoefficientSource B U b hR hσ S) :=
    allocatedLongCoefficientSource_probability B U b hR hσ S
  exact (allocatedCoefficientSplit_measurePreserving B U b hR hσ S).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae (allocatedFrozenCoefficientSource_supported B U b hR hσ S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedPhysicalMixedJet_test_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : AllocatedFrozenCoefficients B U b S →
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) → ℂ)
    (hφ : Measurable (fun p : AllocatedFrozenCoefficients B U b S ×
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) => φ p.1 p.2))
    {C : ℝ} (hbound : ∀ a t, ‖φ a t‖ ≤ C) :
    (∫ a, weights.complexMean (fun v => φ (split a).1
      (canonicalCoefficientJetArrays (root v) (dirs v) rows a)) ∂source) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          φ a₀ (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z) ∂reference ∂frozenSource := by
  have htest : Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      φ p.1 (allocatedMixedJetReconstruct B U b S x u v₀ rows p.1 p.2)) :=
    hφ.comp (measurable_fst.prodMk (allocatedMixedJetReconstruct_measurable B U b S x u v₀ rows))
  calc
    _ = ∫ a, weights.complexMean (fun v => φ (split a).1
        (allocatedMixedJetReconstruct B U b S x u v₀ rows (split a).1
          (allocatedPhysicalLongJetMap B U b S x u v rows a))) ∂source := by
      apply integral_congr_ae
      filter_upwards [allocatedCoefficientSource_frozen_supported B U b hR hσ S] with a ha
      apply congrArg weights.complexMean
      funext v
      rw [allocatedMixedJetReconstruct_physical_split B U b hR hσ S x u v v₀ rows a ha]
    _ = ∫ a₀, ∫ z, weights.complexMean (fun v =>
        (allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z : ℂ) *
          φ a₀ (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z)) ∂reference ∂frozenSource :=
      allocatedPhysicalLongJet_variable_test_mean B U b hR hσ S x u rows s hA hσ1 weights
        (fun _ a₀ z => φ a₀ (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z))
        (fun _ => htest) (fun _ a₀ z => hbound a₀ _)
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a₀
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      exact weights.complexMean_ofReal_mul _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

noncomputable def allocatedDeckMixedTest (a₀ : AllocatedFrozenCoefficients B U b S)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : ℂ :=
  ∫ r, φ ((a₀, t), coefficientDeckJetMap (root v₀) (dirs v₀) rows d r) ∂(deck).toMeasure

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedDeckMixedTest_measurable (hφ : Measurable φ) :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S ×
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) =>
        allocatedDeckMixedTest B U b S x u v₀ rows Q d φ p.1 p.2) :=
  finitePMF_integral_measurable deck _ (fun _ => hφ.comp (measurable_id.prodMk measurable_const))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedDeckMixedTest_norm_le {C : ℝ} (hφ : ∀ p, ‖φ p‖ ≤ C)
    (a₀ : AllocatedFrozenCoefficients B U b S)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    ‖allocatedDeckMixedTest B U b S x u v₀ rows Q d φ a₀ t‖ ≤ C :=
  finitePMF_integral_norm_le deck _ (fun _ => hφ _)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalMixedDeck_test_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel M v = principalResidueLabel M v₀)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p, weights.complexMean (fun v =>
      φ (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
        coefficientDeckJetMap (root v) (dirs v) rows d p.2)) ∂(source).prod (deck).toMeasure) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          allocatedDeckMixedTest B U b S x u v₀ rows Q d φ a₀
            (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z) ∂reference ∂frozenSource := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U b hR hσ S
  have htest (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
      Measurable (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
        CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
        φ (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
          coefficientDeckJetMap (root v) (dirs v) rows d p.2)) :=
    hφ.comp ((((split).measurable.comp measurable_fst).fst.prodMk
      ((canonicalCoefficientJetArrays_measurable (root v) (dirs v) rows).comp measurable_fst)).prodMk
        ((measurable_of_finite (coefficientDeckJetMap (B := Q) (root v) (dirs v) rows d)).comp measurable_snd))
  calc
    _ = ∫ a, weights.complexMean (fun v => ∫ r,
        φ (((split a).1, canonicalCoefficientJetArrays (root v) (dirs v) rows a),
          coefficientDeckJetMap (root v) (dirs v) rows d r) ∂(deck).toMeasure) ∂source :=
      probabilityProduct_finiteMean source (deck).toMeasure weights _ htest (fun _ p => hbound _)
    _ = ∫ a, weights.complexMean (fun v => allocatedDeckMixedTest B U b S x u v₀ rows Q d φ
        (split a).1 (canonicalCoefficientJetArrays (root v) (dirs v) rows a)) ∂source := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      apply weights.complexMean_congr_support
      intro v hv
      let F := fun e => φ (((split a).1, canonicalCoefficientJetArrays (root v) (dirs v) rows a), e)
      have hlaw := allocatedPhysicalDeckJet_law_eq_of_residue B U b S x u v v₀ rows Q M hperiod
        (hresidue v hv) d
      exact (finitePMF_integral_comp deck (coefficientDeckJetMap (root v) (dirs v) rows d) F).trans
        ((congrArg (fun p : PMF (∀ j, O j → Q j → ZMod d) => ∫ e, F e ∂p.toMeasure) hlaw).trans
          (finitePMF_integral_comp deck (coefficientDeckJetMap (root v₀) (dirs v₀) rows d) F).symm)
    _ = _ := allocatedPhysicalMixedJet_test_mean B U b hR hσ S x u v₀ rows s hA hσ1 weights
      (allocatedDeckMixedTest B U b S x u v₀ rows Q d φ)
      (allocatedDeckMixedTest_measurable B U b S x u v₀ rows Q d φ hφ)
      (allocatedDeckMixedTest_norm_le B U b S x u v₀ rows Q d φ hbound)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "pullback" => (fun p : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) =>
  F (Prod.fst (Prod.fst p), coveredJetChart U b hb bW d
    (mixedCoveredJetCoordinates U o d (Prod.snd (Prod.fst p), Prod.snd p))))

omit [Fintype α] [DecidableEq α] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredPullback_measurable (hF : Measurable F) : Measurable pullback := by
  have hchart := (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
    (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  exact hF.comp ((measurable_fst.comp measurable_fst).prodMk
    (hchart.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

noncomputable def allocatedCoveredFixedTest
    (a₀ : AllocatedFrozenCoefficients B U b S) (z : AllocatedLongJetRows B U b S O) : ℂ :=
  allocatedDeckMixedTest B U b S x u v₀ rows Q d pullback a₀
    (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z)

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredFixedTest_measurable (hF : Measurable F) :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F p.1 p.2) :=
  (allocatedDeckMixedTest_measurable B U b S x u v₀ rows Q d pullback
    (allocatedCoveredPullback_measurable B U b S Q hb o bW d F hF)).comp
      (measurable_fst.prodMk (allocatedMixedJetReconstruct_measurable B U b S x u v₀ rows))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredFixedTest_norm_le {C : ℝ} (hF : ∀ p, ‖F p‖ ≤ C)
    (a₀ : AllocatedFrozenCoefficients B U b S) (z : AllocatedLongJetRows B U b S O) :
    ‖allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z‖ ≤ C :=
  allocatedDeckMixedTest_norm_le B U b S x u v₀ rows Q d pullback (fun _ => hF _) a₀ _

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalCovered_test_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel M v = principalResidueLabel M v₀)
    (hF : Measurable F) {C : ℝ} (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, weights.complexMean (fun v => F ((split p.1).1,
      euclideanCoefficientJetMap U (root v) (dirs v) rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
        ∂(source).prod (deck).toMeasure) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z ∂reference ∂frozenSource := by
  have he := allocatedPhysicalMixedDeck_test_mean B U b hR hσ S x u v₀ rows Q d pullback
    s hA hσ1 weights M hperiod hresidue
    (allocatedCoveredPullback_measurable B U b S Q hb o bW d F hF) (fun p => hbound _)
  calc
    _ = ∫ p, weights.complexMean (fun v =>
        pullback (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
          coefficientDeckJetMap (root v) (dirs v) rows d p.2)) ∂(source).prod (deck).toMeasure := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      apply congrArg weights.complexMean
      funext v
      rw [canonicalCoefficientDeckSample_chart U o (root v) (dirs v) rows b hb bW d]
    _ = _ := he

end Erdos3.VectorPolynomial

end

end OAI
