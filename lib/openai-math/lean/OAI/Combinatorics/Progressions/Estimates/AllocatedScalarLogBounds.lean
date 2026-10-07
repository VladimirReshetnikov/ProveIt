/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.AllocatedQuotientSupport
import OAI.Combinatorics.Progressions.Lattices.IntegerInterpolationExpBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedLayerCenters (j : Fin m) :
    I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ :=
  allocatedArrayCenters Subtype.val (layerSamplerBox B U b S) (layerContinuousPrincipalSlots B j) (R j)

noncomputable def allocatedLayerWidths (j : Fin m) :
    I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ :=
  allocatedArrayWidths Subtype.val (layerSamplerBox B U b S) (layerContinuousPrincipalSlots B j)
    (constantCoefficientSlot _ _) (R j) (σ j)

include hR hσ in
theorem allocatedLayerWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedLayerWidths B U b S j i d :=
  allocatedArrayWidths_pos _ _ (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    _ _ (hR j) (hσ j) i d

noncomputable def allocatedLayerIntegerPMFs (j : Fin m) :
    Fin (n j) → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → PMF ℤ :=
  allocatedProjectionPMFs (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include hR hσ in
theorem allocatedLayerColumns_chart (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (j : Fin m) (d) (x) (hx : mixedCoefficientDensity (fun i => allocatedLayerCenters B U b S j i d)
      (fun i => allocatedLayerWidths B U b S j i d)
      (fun i => allocatedLayerIntegerPMFs B U b hR hσ S j i d) x ≠ 0) :
    normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) ∈
      standardLatticeSmallBox (J j) := by
  exact allocatedArrayColumns_chart (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) d x hx

theorem allocatedLayerSupported_polynomial_chart (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (j : Fin m) (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x : LayerSamplerVariables G I n B → ℝ) (hx : ∀ v, |x v| ≤ layerSamplerBox B U b S v) :
    mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x ∈
      standardLatticeSmallBox (J j) := by
  exact allocatedArraySupported_polynomial_chart (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) a ha x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerCenters_constant (j : Fin m) (i : I j) :
    allocatedLayerCenters B U b S j i (constantCoefficientSlot _ _) = 0 := by
  classical
  simp only [allocatedLayerCenters, allocatedArrayCenters, coefficientProfileCenter,
    ite_eq_right (layerContinuousPrincipalSlots_not_constant B j i), zero_div]

theorem allocatedLayerWidths_constant (j : Fin m) (i : I j) :
    allocatedLayerWidths B U b S j i (constantCoefficientSlot _ _) = R j / 4 := by
  classical
  simp [allocatedLayerWidths, allocatedArrayWidths, coefficientProfileWidth,
    constantCoefficientSlot, monomialScale]

theorem allocatedLayerIntegerPMFs_constant (j : Fin m) (i : Fin (n j)) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i (constantCoefficientSlot _ _) =
      latticeConstantMass (euclideanSubspace (U j)) (b j) (fun _ => R j / 4)
        (fun _ => div_pos (hR j) (by norm_num)) i := by
  classical
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF,
    ite_true, latticeConstantMass]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerIntegerInterpolationCap (R σ : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  integerPolynomialInterpolationCap (j.val+1) L (layerTailDegree m) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

noncomputable def allocatedLayerIntegerInterpolationLip (R σ : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  integerPolynomialInterpolationLip (j.val+1) L (layerTailDegree m) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedLayerIntegerInterpolation (j : Fin m) (i : Fin (n j))
    (d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ → ℝ :=
  integerPolynomialInterpolation (layerIntegerPrincipalSlots (G := G) B j i) (constantCoefficientSlot _ _)
    (j.val+1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (layerSamplerBox B U b S) Subtype.val
    (R j / 4) (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))) d

theorem allocatedLayerIntegerInterpolation_spec (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    IsIntegerMassInterpolation (basisAxisScale (b j) i) (allocatedLayerIntegerPMFs B U b hR hσ S j i d)
      (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j i)
      (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i)
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  exact integerPolynomialInterpolation_spec (layerIntegerPrincipalSlots (G := G) B j i) (constantCoefficientSlot _ _)
    (j.val+1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
    S.positive (layerSamplerBox B U b S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j)) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (div_pos (hR j) (by norm_num)) (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _)
    (S.gap j i) (S.width j) d

theorem allocatedLayerIntegerInterpolation_lipschitz (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    LipschitzWith (Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i))
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  apply (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).lipschitz
  unfold allocatedLayerIntegerInterpolationLip integerPolynomialInterpolationLip
    constantIntegerInterpolationLip principalAxisInterpolationLip tailAxisInterpolationLip
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "profile" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

noncomputable def allocatedPrincipalNormalizedSource : NormalizedScalarCubeSource Empty :=
  principalNormalizedSource
    (K := (basisAxisScale (basis j) i : ℝ)) (T := (S.value : ℝ) ^ (j.val + 1))
    (γ := profile)
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive))

theorem allocatedPrincipalNormalizedSource_law (b : B ⟨j, Sum.inr i⟩) :
    (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.toPMF.map
      (fun x => (x none : ℤ)) =
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) := by
  have hmem : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b ∈
      layerIntegerPrincipalSlots (G := G) B j i :=
    (mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩
  have hne : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b ≠
      constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1) := by
    intro he
    rw [he] at hmem
    exact (layerIntegerPrincipalSlots_not_constant B j i) hmem
  unfold allocatedPrincipalNormalizedSource
  rw [principalNormalizedSource_law]
  symm
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF]
  split_ifs with hc hp
  · exact False.elim (hne hc)
  · simp only [integerAxisPrincipalPMF, hactive, ↓reduceDIte]
  · exact False.elim (hp hmem)

theorem allocatedPrincipalNormalizedSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (allocatedPrincipalNormalizedSource B U basis hR S j i hactive) A
      (scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1) :=
  principalNormalizedSource_primitive _ _ _ _ A

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerCommonCap (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  1 + ∑ i, Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i)

noncomputable def allocatedLayerCommonLip (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  ∑ i, Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i)

noncomputable def allocatedLayerWidthFloor (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  Real.toNNReal (allocatedWidthFloor (R j) (σ j) L (j.val+1)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

theorem allocatedLayerCommonCap_one_le (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) :
    1 ≤ allocatedLayerCommonCap (G := G) B R σ L j := le_add_of_nonneg_right (by positivity)

theorem allocatedLayerWidthFloor_pos {R σ : Fin m → ℝ}
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) {L : ℕ} (hL : 0 < L) (j : Fin m) :
    0 < allocatedLayerWidthFloor (G := G) B R σ L j := by
  apply Real.toNNReal_pos.mpr
  exact allocatedWidthFloor_pos (hR j) (hσ j) hL _ _

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerWidths_floor (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : I j) (d) :
    (allocatedLayerWidthFloor (G := G) B R σ S.value j : ℝ) ≤ allocatedLayerWidths B U b S j i d := by
  rw [allocatedLayerWidthFloor, Real.coe_toNNReal _ (allocatedWidthFloor_pos (hR j) (hσ j) S.positive _ _).le]
  exact allocatedArrayWidths_floor Subtype.val (layerSamplerBox B U b S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (hR j) (hσ j) S.positive
    (layerSamplerBox_le B U b S) (fun d => d.property) i d

theorem allocatedLayerInterpolation_common_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    (∀ x, 0 ≤ allocatedLayerIntegerInterpolation B U b S j i d x ∧
      allocatedLayerIntegerInterpolation B U b S j i d x ≤ allocatedLayerCommonCap (G := G) B R σ S.value j) ∧
    LipschitzWith (allocatedLayerCommonLip (G := G) B R σ S.value j)
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  have hspec := allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d
  have hcap : Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j i) ≤
      allocatedLayerCommonCap (G := G) B R σ S.value j := by
    apply le_trans (Finset.single_le_sum
      (f := fun t : Fin (n j) => Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j t))
      (fun _ _ => zero_le) (Finset.mem_univ i))
    exact le_add_of_nonneg_left (by norm_num)
  have hlip : Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i) ≤
      allocatedLayerCommonLip (G := G) B R σ S.value j := by
    unfold allocatedLayerCommonLip
    exact Finset.single_le_sum
      (f := fun t : Fin (n j) => Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j t))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  refine ⟨?_, (allocatedLayerIntegerInterpolation_lipschitz B U b S hR hσ j i d).weaken hlip⟩
  intro x
  exact ⟨(hspec.2.1 x).1, (hspec.2.1 x).2.trans ((Real.le_coe_toNNReal _).trans (by exact_mod_cast hcap))⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem sum_le_exp_of_card_and_uniform_bound {I : Type*} [Fintype I]
    (f : I → ℝ) {P Q : ℝ} (hQ : 0 ≤ Q) (hcard : (Fintype.card I : ℝ) ≤ P)
    (hf : ∀ i, f i ≤ Real.exp Q) : (∑ i, f i) ≤ Real.exp (P + P * Q) := by
  have h := sum_le_exp_card_add_sum f (fun _ => Q) (fun _ => hQ) hf
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact h.trans (Real.exp_le_exp.mpr (add_le_add hcard (mul_le_mul_of_nonneg_right hcard hQ)))

def allocatedScalarLog (m : ℕ) (P : ℝ) : ℝ :=
  7 * integerInterpolationLogEnvelope (layerTailDegree m) (4 * (P+8))

def allocatedCommonLog (m : ℕ) (P : ℝ) : ℝ := P + P * allocatedScalarLog m P + 1

def allocatedWidthLog (m : ℕ) (P : ℝ) : ℝ := ((m : ℝ)+4)*(P+8)

theorem allocatedScalarLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedScalarLog m P := by
  unfold allocatedScalarLog integerInterpolationLogEnvelope
  positivity

theorem allocatedCommonLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedCommonLog m P := by
  have h := allocatedScalarLog_nonneg m hP
  unfold allocatedCommonLog
  positivity

theorem allocatedWidthLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedWidthLog m P := by
  unfold allocatedWidthLog
  positivity

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerIntegerInterpolation_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P)
    (i : Fin (n j)) :
    allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i ≤ Real.exp (allocatedScalarLog m P) ∧
      allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i ≤ Real.exp (allocatedScalarLog m P) := by
  have hprincipalCount : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ P :=
    (Nat.cast_le.mpr (layerIntegerPrincipalSlots (G := G) B j i).card_le_univ).trans hcount
  have hp := allocatedProfile_inverse_exp_bounds _ hP hR hσ hRP hσP hprincipalCount
  have ht := allocatedProfile_inverse_exp_bounds _ hP hR hσ hRP hσP hcount
  have hQ : 0 ≤ 4*(P+8) := by positivity
  have hPQ : P ≤ 4*(P+8) := by linarith
  have he := Real.exp_le_exp.mpr hPQ
  have h := integerPolynomialInterpolation_exp_bounds (layerTailDegree m) (j.val+1) L (layerTailDegree m)
    (layerDegree_le_tailDegree j) le_rfl hQ (hAP.trans he) (hLP.trans he)
    (div_pos hR (by norm_num)) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hp.1 hp.2.1 ht.2.2.2
  have henv : 0 ≤ integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8)) := by
    unfold integerInterpolationLogEnvelope
    positivity
  refine ⟨h.1.trans (Real.exp_le_exp.mpr ?_), h.2⟩
  change 3 * integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8)) ≤
    7 * integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8))
  linarith

theorem allocatedLayerCommonInterpolation_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hn : (n j : ℝ) ≤ P) (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedLayerCommonCap (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedCommonLog m P) ∧
      (allocatedLayerCommonLip (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedCommonLog m P) := by
  have h := allocatedLayerIntegerInterpolation_exp_bounds B R σ L j hP hR hσ hRP hσP hcount hAP hLP
  have hcard : (Fintype.card (Fin (n j)) : ℝ) ≤ P := by simpa only [Fintype.card_fin] using hn
  have hc := sum_le_exp_of_card_and_uniform_bound
    (fun i => (Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i) : ℝ))
    (allocatedScalarLog_nonneg m hP) hcard (fun i => coe_toNNReal_le_exp (h i).1)
  have hl := sum_le_exp_of_card_and_uniform_bound
    (fun i => (Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i) : ℝ))
    (allocatedScalarLog_nonneg m hP) hcard (fun i => coe_toNNReal_le_exp (h i).2)
  constructor
  · simp only [allocatedLayerCommonCap, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
    exact one_add_le_exp_succ (by have h := allocatedScalarLog_nonneg m hP; positivity) hc
  · simp only [allocatedLayerCommonLip, NNReal.coe_sum]
    exact hl.trans (Real.exp_le_exp.mpr (by unfold allocatedCommonLog; linarith))

theorem allocatedLayerWidthFloor_inv_exp (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hLP : (L : ℝ) ≤ Real.exp P) :
    (((allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp (allocatedWidthLog m P) := by
  rw [NNReal.coe_inv, allocatedLayerWidthFloor,
    Real.coe_toNNReal _ (allocatedWidthFloor_pos hR hσ hL _ _).le]
  exact allocatedWidthFloor_inverse_exp_bound L (j.val+1) m _ (Nat.succ_le_of_lt j.isLt)
    hP hR hσ hRP hσP hcount hLP

end VectorPolynomial
end Erdos3

end

end OAI
