import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedFrozenTupleWeights :
    FiniteProbabilityWeights (PrincipalAxisTuples (B := B) (h := degree) (α := α) grid sides) :=
  principalTupleWeights (fun d : {d // grid d} => B d.val) (fun d => degree d.val)
    (principalAxisLength grid sides) (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)

noncomputable def allocatedLongTupleWeights :
    FiniteProbabilityWeights (PrincipalAxisTuples (B := B) (h := degree) (α := α) (fun d => ¬grid d) sides) :=
  principalTupleWeights (fun d : {d // ¬grid d} => B d.val) (fun d => degree d.val)
    (principalAxisLength (fun d => ¬grid d) sides)
    (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)

local notation "wholeWeight" => principalTupleWeights B degree sides (allocatedPrincipalSides_pos B U basis S)
local notation "frozenWeight" => allocatedFrozenTupleWeights (α := α) B U basis S
local notation "longWeight" => allocatedLongTupleWeights (α := α) B U basis S
local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "longSource" => allocatedLongCoefficientSource B U basis hR hσ S
local notation "reconstruct" => MeasurableEquiv.symm (allocatedCoefficientSplit B U basis S)

variable (f : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n →
  PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) → ℂ)

theorem allocatedJoint_source_partition :
    (∫ a, (wholeWeight).complexMean (f a) ∂source) =
      ∫ a, (frozenWeight).complexMean (fun u => (longWeight).complexMean
        (fun v => f (reconstruct a) (principalAxisJoin grid u v))) ∂(frozenSource).prod longSource := by
  calc
    _ = ∫ a, (wholeWeight).complexMean (f (reconstruct a)) ∂(frozenSource).prod longSource :=
      (allocatedCoefficientReconstruct_measurePreserving B U basis hR hσ S).integral_comp' _ |>.symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun a =>
      principalTupleWeights_partition grid sides (allocatedPrincipalSides_pos B U basis S)
        (f (reconstruct a))))

theorem allocatedJoint_source_residues (M : ℕ) [NeZero M] (hM : 0 < M)
    (hsize : (Fintype.card α+1)*M ≤ S.value) :
    (∫ a, (wholeWeight).complexMean (f a) ∂source) =
      ∫ a, (frozenWeight).complexMean (fun u =>
        ((longWeight).fiberLaw (principalResidueLabel M)).complexMean (fun r =>
          (principalResidueWeights (fun d : {d // ¬grid d} => B d.val) (fun d => degree d.val)
            (principalAxisLength (fun d => ¬grid d) sides)
            (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩) M hM r
            (fun j => by rw [allocatedPrincipalSides_long_restricted B U basis S j]; exact hsize)).complexMean
              (fun v => f (reconstruct a) (principalAxisJoin grid u v)))) ∂(frozenSource).prod longSource := by
  calc
    _ = ∫ a, (wholeWeight).complexMean (f (reconstruct a)) ∂(frozenSource).prod longSource :=
      (allocatedCoefficientReconstruct_measurePreserving B U basis hR hσ S).integral_comp' _ |>.symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun a =>
      allocatedPrincipal_partition_residues B U basis S M hM hsize (f (reconstruct a))))

theorem allocatedJoint_frozen_integral
    (hf : ∀ y, Measurable (fun a => f a y)) {C : ℝ} (hbound : ∀ a y, ‖f a y‖ ≤ C) :
    (∫ a, (wholeWeight).complexMean (f a) ∂source) =
      ∫ a₀, (frozenWeight).complexMean (fun u =>
        ∫ a₁, (longWeight).complexMean (fun v =>
          f (reconstruct (a₀, a₁)) (principalAxisJoin grid u v)) ∂longSource) ∂frozenSource := by
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U basis hR hσ S
  let : IsProbabilityMeasure longSource := allocatedLongCoefficientSource_probability B U basis hR hσ S
  have hpiece (y : PrincipalIntegerTuples B degree α sides) :
      Integrable (fun a => f (reconstruct a) y) ((frozenSource).prod longSource) :=
    (integrable_const C).mono' ((hf y).comp (reconstruct).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => hbound (reconstruct a) y))
  have hi : Integrable (fun a => (frozenWeight).complexMean (fun u => (longWeight).complexMean
      (fun v => f (reconstruct a) (principalAxisJoin grid u v)))) ((frozenSource).prod longSource) :=
    (frozenWeight).complexMean_integrable _ _ (fun u => (longWeight).complexMean_integrable _ _
      (fun v => hpiece (principalAxisJoin grid u v)))
  rw [allocatedJoint_source_partition B U basis hR hσ S f, integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a₀
  apply (frozenWeight).integral_complexMean
  intro u
  apply (longWeight).complexMean_integrable
  intro v
  exact (integrable_const C).mono'
    ((hf (principalAxisJoin grid u v)).comp
      ((reconstruct).measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a₁ => hbound (reconstruct (a₀, a₁)) (principalAxisJoin grid u v)))

end Erdos3.VectorPolynomial

end

end OAI
