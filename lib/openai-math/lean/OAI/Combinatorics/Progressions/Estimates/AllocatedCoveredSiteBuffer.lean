import OAI.Combinatorics.Progressions.Probability.AllocatedReferenceBufferMass
import OAI.Combinatorics.Progressions.Probability.AllocatedSiteEnvelopeMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

local notation "radius" => idealSiteEnvelopeRadius α m
local notation "reference" => allocatedLongJetReference B U b S jets
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)

variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)

local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))

noncomputable def allocatedMaskedSiteEnvelope
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) (z : AllocatedLongJetRows B U b S jets) : ℝ :=
  (∏ a, allocatedLongJetMask B U b S x jetRows modulus residue a (z a)) *
    allocatedIdealSiteEnvelope B U b S z / scale

theorem allocatedMaskedSiteEnvelope_measurable
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    Measurable (allocatedMaskedSiteEnvelope B U b S x modulus residue) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U b S jets =>
      ∏ a, allocatedLongJetMask B U b S x jetRows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U b S x jetRows modulus residue a).comp (measurable_pi_apply a))
  exact (hm.mul (allocatedIdealSiteEnvelope_measurable B U b S)).div_const _

theorem allocatedMaskedSiteEnvelope_abs_le
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) (hR : ∀ j, 0 < R j)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ≤ C)
    (z : AllocatedLongJetRows B U b S jets) :
    |allocatedMaskedSiteEnvelope B U b S x modulus residue z| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) * (allocatedIdealSiteEnvelope B U b S z / scale) := by
  have hs : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  unfold allocatedMaskedSiteEnvelope
  rw [abs_div, abs_mul, abs_of_nonneg (allocatedIdealSiteEnvelope_nonneg B U b S hR z), abs_of_pos hs]
  calc
    _ ≤ (C ^ Fintype.card (LayerSamplerAxis I n) * allocatedIdealSiteEnvelope B U b S z) / scale :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (allocatedLongJetMask_product_bound B U b S x jetRows modulus residue hC hm z)
          (allocatedIdealSiteEnvelope_nonneg B U b S hR z)) hs.le
    _ = _ := by ring

theorem allocatedMaskedSiteEnvelope_integrable
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) (hR : ∀ j, 0 < R j)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ≤ C) :
    Integrable (allocatedMaskedSiteEnvelope B U b S x modulus residue) reference := by
  have hmajor := ((allocatedIdealSiteEnvelope_integrable (α := α) B U b S hR).div_const scale).const_mul
    (C ^ Fintype.card (LayerSamplerAxis I n))
  apply hmajor.mono' (allocatedMaskedSiteEnvelope_measurable B U b S x modulus residue).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  exact allocatedMaskedSiteEnvelope_abs_le B U b S x modulus residue hR hC hm z

theorem allocatedMaskedSiteEnvelope_integral_abs_le
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) (hR : ∀ j, 0 < R j)
    (hσ1 : ∀ j, σ j ≤ 1) {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ≤ C) :
    (∫ z, |allocatedMaskedSiteEnvelope B U b S x modulus residue z| ∂reference) ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (2 * radius + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) := by
  have hmajor := ((allocatedIdealSiteEnvelope_integrable (α := α) B U b S hR).div_const scale).const_mul
    (C ^ Fintype.card (LayerSamplerAxis I n))
  calc
    _ ≤ ∫ z, C ^ Fintype.card (LayerSamplerAxis I n) *
        (allocatedIdealSiteEnvelope B U b S z / scale) ∂reference :=
      integral_mono (allocatedMaskedSiteEnvelope_integrable B U b S x modulus residue hR hC hm).abs
        hmajor (allocatedMaskedSiteEnvelope_abs_le B U b S x modulus residue hR hC hm)
    _ = C ^ Fintype.card (LayerSamplerAxis I n) *
        (∫ z, allocatedIdealSiteEnvelope B U b S z / scale ∂reference) := by rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (allocatedIdealSiteEnvelope_normalized_integral_le B U b S hR hσ1)
      (pow_nonneg (zero_le_one.trans hC) _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

local notation "radius" => idealSiteEnvelopeRadius α m
local notation "reference" => allocatedLongJetReference B U b S jets
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := jets) a)

variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)

local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Module.Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j : Fin m, BoundedBooleanJet α (j.val + 1) → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))

include hΩm hΩ in
theorem allocatedCoveredSiteEnvelope_integral_abs_le
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) (hσ1 : ∀ j, σ j ≤ 1)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ≤ C) :
    (∫ y, |allocatedCoveredProfileDensity B U b hR hσ S x u v jetRows hb o bW d Ω
      (allocatedMaskedSiteEnvelope B U b S x modulus residue) y| ∂haar) ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (2 * radius + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) := by
  exact (allocatedCoveredProfileDensity_integral_abs B U b hR hσ S x u v jetRows
    hb o bW d Ω hΩm hΩ ν (allocatedMaskedSiteEnvelope B U b S x modulus residue)
    (allocatedMaskedSiteEnvelope_measurable B U b S x modulus residue)
    (allocatedMaskedSiteEnvelope_integrable B U b S x modulus residue hR hC hm)).trans
      (allocatedMaskedSiteEnvelope_integral_abs_le B U b S x modulus residue hR hσ1 hC hm)

include hΩm hΩ in
theorem allocatedCoveredSiteEnvelope_goodKernel_mass
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) (hσ1 : ∀ j, σ j ≤ 1)
    {M : ℕ} {κ p : ℝ} (hM : 0 < M) (selection : α ↪ G)
    (hx : GoodScalarKernelTuple selection κ M x) (hq : Fintype.card α ≤ m + 1)
    (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p) :
    (∫ y, |allocatedCoveredProfileDensity B U b hR hσ S x u v jetRows hb o bW d Ω
      (allocatedMaskedSiteEnvelope B U b S x modulus residue) y| ∂haar) ≤
      Real.exp ((Fintype.card (LayerSamplerAxis I n) : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * p) +
        (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) : ℝ) *
          (((m : ℝ) + 3) * Fintype.card α + 5)) := by
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * p
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hp
  have hC : 1 ≤ Real.exp w := Real.one_le_exp_iff.mpr hw
  have hm (j : Fin m) (z : jets j → ℤ) :
      0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue j) z ≤ Real.exp w := by
    exact ⟨(allocatedIntegerKernelMask_bound B U b S x jetRows hM selection hx hq
      (fun _ => Subtype.val_injective) (fun _ z => z.property) j modulus (residue j) z).1,
      allocatedIntegerKernelMask_le_exp B U b S x jetRows hM selection hx hq
        (fun _ => Subtype.val_injective) (fun _ z => z.property) hMp j modulus (residue j) z⟩
  apply (allocatedCoveredSiteEnvelope_integral_abs_le B U b S x modulus hR hσ
    u v hb o bW d Ω hΩm hΩ ν residue hσ1 hC hm).trans
  calc
    _ ≤ (Real.exp w) ^ Fintype.card (LayerSamplerAxis I n) *
        Real.exp ((Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) : ℝ) *
          (((m : ℝ) + 3) * Fintype.card α + 5)) :=
      mul_le_mul_of_nonneg_left (idealSiteEnvelopeRadius_volume_le_exp α m _) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "invVolume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))⁻¹
local notation "radius" => idealSiteEnvelopeRadius α m

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "buffer" => allocatedSiteBuffer (α := α) B U b S
local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v jetRows hb o bW d quarter

theorem allocatedCoveredSiteEnvelope_le_buffer_majorant (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (A : ℝ≥0)
    (hA : ∀ (z : AllocatedLongJetRows B U b S jets) (r : ∀ j, jets j → Q j → ZMod d),
      |∏ a, allocatedLongJetMask B U b S x jetRows modulus residue a (z a)| *
        coefficientDeckJetDensity root dirs jetRows d r ≤ A)
    (y : EuclideanJetLayers U jets) :
    |profile (allocatedMaskedSiteEnvelope B U b S x modulus residue) y| ≤
      allocatedProfileErrorMajorant B U b S o hR hσ x u v jetRows A buffer (fun _ => 0) d y := by
  have hquarter (j : Fin m) (_t : jets j) :
      standardLatticeClosedQuarterBox (J j) ⊆ standardLatticeSmallBox (J j) :=
    standardLatticeClosedQuarterBox_subset_smallBox (J j)
  have hcomp := allocatedCoveredProfileDensity_abs_mono B U b S hR hσ x u v jetRows hb o bW d
    quarter hquarter (allocatedMaskedSiteEnvelope B U b S x modulus residue)
    (allocatedLongProfileDensity B U b S x jetRows modulus residue buffer) (by
      intro z
      simp only [allocatedMaskedSiteEnvelope, allocatedLongProfileDensity, abs_div, abs_mul,
        abs_of_nonneg (allocatedIdealSiteEnvelope_nonneg B U b S hR z),
        abs_of_nonneg (allocatedSiteBuffer_range B U b S hR _).1]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (allocatedIdealSiteEnvelope_le_buffer B U b S hR z) (abs_nonneg _))
        (abs_nonneg _)) y
  have hmajor := allocatedProfileDifference_le_majorant B U b S o hR hσ x u v jetRows
    hb bW d modulus residue A hA buffer (fun _ => 0) y
  rw [congrFun (allocatedCoveredProfileDensity_sub B U b hR hσ S x u v jetRows hb o bW d
    quarter hquarter (allocatedLongProfileDensity B U b S x jetRows modulus residue buffer)
      (allocatedLongProfileDensity B U b S x jetRows modulus residue (fun _ => 0))) y] at hmajor
  have hsub : (fun z => allocatedLongProfileDensity B U b S x jetRows modulus residue buffer z -
      allocatedLongProfileDensity B U b S x jetRows modulus residue (fun _ => 0) z) =
      allocatedLongProfileDensity B U b S x jetRows modulus residue buffer := by
    funext z
    simp only [allocatedLongProfileDensity, mul_zero, zero_div, sub_zero]
  rw [hsub] at hmajor
  exact hcomp.trans hmajor

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))

include hb bW in
theorem allocatedSiteBuffer_majorant_integrable_mass (hσ1 : ∀ j, σ j ≤ 1)
    (A M : ℝ≥0) (hInv : ∀ j, (R j)⁻¹ ≤ M) (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Integrable (allocatedProfileErrorMajorant B U b S o hR hσ x u v jetRows A buffer (fun _ => 0) d) haar ∧
      (∫ y, allocatedProfileErrorMajorant B U b S o hR hσ x u v jetRows A buffer (fun _ => 0) d y ∂haar) ≤
        (A : ℝ) * Real.exp ((Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) : ℝ) *
          (((m : ℝ) + 3) * Fintype.card α + 6)) := by
  have heq : (fun w : output → ℝ => |buffer w - 0|) = buffer := by
    funext w
    rw [sub_zero, abs_of_nonneg (allocatedSiteBuffer_range B U b S hR w).1]
  have hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun w : output → ℝ => |buffer w - 0|))
      (allocatedLongJetReference B U b S jets) := by
    rw [heq]
    exact (allocatedSiteBuffer_integrable_mass B U b S hR hσ1).1
  have hm := allocatedProfileErrorMajorant_integrable_mass (Cg := 0) (Kg := 0) B U b S o hR hσ x u v jetRows hb bW d ν
    A buffer (fun _ => 0) hi (allocatedSiteBuffer_lipschitz B U b S hR M hInv) (LipschitzWith.const 0)
    (allocatedSiteBuffer_abs_le B U b S hR) (by intro _; simp) C V hC hV
  refine ⟨hm.1, hm.2.trans ?_⟩
  rw [heq]
  exact mul_le_mul_of_nonneg_left (allocatedSiteBuffer_integral_le_exp B U b S hR hσ1) A.coe_nonneg

end Erdos3.VectorPolynomial

end

end OAI
