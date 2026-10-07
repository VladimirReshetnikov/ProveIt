/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

def AllocatedFrozenSupported (a : AllocatedFrozenCoefficients B U b S) : Prop :=
  ∀ (j : Fin m) (i : Fin (n j)) (hi : grid ⟨j, Sum.inr i⟩) d,
    a ⟨⟨j, Sum.inr i⟩, hi⟩ d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i d).support

theorem allocatedFrozenCoefficientSource_supported :
    ∀ᵐ a ∂allocatedFrozenCoefficientSource B U b hR hσ S,
      AllocatedFrozenSupported B U b hR hσ S a := by
  classical
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U b hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U b hR hσ S
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro hi
  have hrow : ∀ᵐ a ∂allocatedCoefficientAxisLaw B U b hR hσ S ⟨j, Sum.inr i⟩,
      ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i d).support := by
    change ∀ᵐ a ∂Measure.pi (fun d => (allocatedLayerIntegerPMFs B U b hR hσ S j i d).toMeasure), _
    exact ae_all_iff.mpr (fun d => (Measure.quasiMeasurePreserving_eval _ d).ae (pmf_support_ae _))
  exact (Measure.quasiMeasurePreserving_eval
    (fun a : {a // grid a} => allocatedCoefficientAxisLaw B U b hR hσ S a.val)
    ⟨⟨j, Sum.inr i⟩, hi⟩).ae hrow

abbrev AllocatedFrozenJetRows (O : Fin m → Type*) :=
  ∀ a : {a // grid a}, CoefficientJetAxisRow O a.val

variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

noncomputable def allocatedFrozenJetMap (a : AllocatedFrozenCoefficients B U b S) :
    AllocatedFrozenJetRows B U b S O :=
  fun i => coefficientJetAxisMap (allocatedPartitionedJetMatrix B U b S x u v rows) i.val (a i)

theorem allocatedFrozenJetMap_measurable [∀ j, Fintype (O j)] :
    Measurable (allocatedFrozenJetMap B U b S x u v rows) :=
  Measurable.of_eval (fun i =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U b S x u v rows) i.val).comp
      (measurable_pi_apply i))

theorem allocatedFrozenJetMap_eq_of_supported (a : AllocatedFrozenCoefficients B U b S)
    (ha : AllocatedFrozenSupported B U b hR hσ S a) :
    allocatedFrozenJetMap B U b S x u v rows a = allocatedFrozenJetMap B U b S x u w rows a := by
  funext i
  rcases i with ⟨⟨j, i | i⟩, hi⟩
  · exact False.elim hi
  · exact allocatedGridAxis_jet_frozen B U b S hR hσ j i hi
      (a ⟨⟨j, Sum.inr i⟩, hi⟩) (ha j i hi) (fun g t => (g, t))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (principalTupleIntegers v) (principalTupleIntegers w) (rows j)

theorem allocatedFrozenJetMap_ae_eq :
    allocatedFrozenJetMap B U b S x u v rows =ᵐ[allocatedFrozenCoefficientSource B U b hR hσ S]
      allocatedFrozenJetMap B U b S x u w rows :=
  (allocatedFrozenCoefficientSource_supported B U b hR hσ S).mono (fun a ha =>
    allocatedFrozenJetMap_eq_of_supported B U b hR hσ S x u v w rows a ha)

theorem allocatedPhysicalJet_grid_reconstruct
    (a₀ : AllocatedFrozenCoefficients B U b S) (a₁ : AllocatedLongCoefficients B U b S)
    (i : {a // grid a}) :
    coefficientJetAxisEquiv O I n
      (canonicalCoefficientJetArrays
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows
        ((allocatedCoefficientSplit B U b S).symm (a₀, a₁))) i.val =
      allocatedFrozenJetMap B U b S x u v rows a₀ i := by
  rw [canonicalCoefficientJetArrays_axis]
  have hm : (fun j => boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v))
      (j.val + 1) (rows j)) = allocatedPartitionedJetMatrix B U b S x u v rows :=
    funext (fun j => (allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j).symm)
  have hc : coefficientAxisEquiv (LayerSamplerVariables G I n B) I n
      ((allocatedCoefficientSplit B U b S).symm (a₀, a₁)) i.val = a₀ i :=
    coefficientAxisSplitEquiv_symm_left grid a₀ a₁ i
  rw [hm, hc]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
