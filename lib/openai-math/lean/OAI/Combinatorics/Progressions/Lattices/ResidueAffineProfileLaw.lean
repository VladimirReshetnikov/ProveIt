import OAI.Combinatorics.Progressions.Geometry.PhysicalSpatialScales

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

noncomputable def shiftedUnitProfile {I : Type*} [Fintype I] (a S : I → ℝ) : (I → ℝ) → ℝ :=
  affineProductProfile (fun i => a i / S i) (fun _ => 1)

theorem shiftedUnitProfile_nonneg {I : Type*} [Fintype I] (a S : I → ℝ) (x : I → ℝ) :
    0 ≤ shiftedUnitProfile a S x :=
  affineProductProfile_nonneg _ _ (fun _ => zero_lt_one) x

theorem shiftedUnitProfile_weight {I : Type*} [Fintype I] (a S : I → ℝ) (z : I → ℤ) :
    coefficientWeight (shiftedUnitProfile a S) S z = rectangularWeight (smoothProductProfile I) a S z := by
  simp only [coefficientWeight, shiftedUnitProfile, affineProductProfile_eq, profileWidthFactor,
    inv_one, Finset.prod_const_one, one_mul, div_one, rectangularWeight]
  congr 1
  funext i
  exact (sub_div (z i : ℝ) (a i) (S i)).symm

theorem shiftedUnitProfile_mass {I : Type*} [Fintype I] (a S : I → ℝ) :
    coefficientWeightSum (shiftedUnitProfile a S) S = shiftedSmoothProductMass a S := by
  unfold coefficientWeightSum shiftedSmoothProductMass
  simp_rw [shiftedUnitProfile_weight]

theorem shiftedUnitProfile_integral {I : Type*} [Fintype I] (a S : I → ℝ) :
    (∫ x, shiftedUnitProfile a S x) = 1 :=
  affineProductProfile_integral _ _ (fun _ => zero_lt_one)

theorem shiftedUnitProfile_lipschitz {I : Type*} [Fintype I] (a S : I → ℝ) :
    LipschitzWith (affineProductProfileLip I 1) (shiftedUnitProfile a S) :=
  affineProductProfile_lipschitz _ _ zero_lt_one (fun _ => le_rfl)

theorem shiftedUnitProfile_cap {I : Type*} [Fintype I] (a S : I → ℝ) (x : I → ℝ) :
    ‖shiftedUnitProfile a S x‖ ≤ 1 := by
  simpa only [shiftedUnitProfile, inv_one, one_pow] using
    affineProductProfile_cap (fun i => a i / S i) (fun _ => 1) zero_lt_one (fun _ => le_rfl) x

theorem shiftedUnitProfile_support {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (ha : ∀ i, |a i| ≤ S i) :
    ∀ x, 2 < ‖x‖ → shiftedUnitProfile a S x = 0 := by
  apply affineProductProfile_zero_outside _ _ (fun _ => zero_lt_one) (by norm_num)
  intro i
  have h : |a i / S i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hS i)]
    exact (div_le_one (hS i)).mpr (ha i)
  linarith

theorem coefficientPMF_shiftedUnitProfile {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) {r : ℝ}
    (hsupport : ∀ x, r < ‖x‖ → shiftedUnitProfile a S x = 0)
    (hZ : 0 < shiftedSmoothProductMass a S) :
    coefficientPMF (shiftedUnitProfile a S) (shiftedUnitProfile_nonneg a S) S hS hsupport
        (by rw [shiftedUnitProfile_mass]; exact hZ) =
      shiftedSmoothProductPMF a S hS hZ := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [coefficientPMF_apply, shiftedSmoothProductPMF_toReal, shiftedUnitProfile_weight, shiftedUnitProfile_mass]

theorem shiftedUnitProfile_residue {K X : Type*} [Fintype K] [Fintype X]
    (residue : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z) :
    shiftedUnitProfile (residueProfileCenter residue modulus) (residueProfileWidth modulus V) =
      affineProductProfile (fun z => -(residue z : ℝ) / V z) (fun _ => 1) := by
  unfold shiftedUnitProfile
  congr 1
  funext z
  have hq : (modulus z.2 : ℝ) ≠ 0 := by exact_mod_cast (hmodulus z.2).ne'
  unfold residueProfileCenter residueProfileWidth
  field_simp [(hV z).ne']

theorem residueSmoothIndexPMF_affine {K X : Type*} [Fintype K] [Fintype X]
    (residue : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (ha : ∀ z, |residueProfileCenter residue modulus z| ≤ residueProfileWidth modulus V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus V)) :
    residueSmoothIndexPMF residue modulus hmodulus V hV hZ =
      coefficientPMF (shiftedUnitProfile (residueProfileCenter residue modulus) (residueProfileWidth modulus V))
        (shiftedUnitProfile_nonneg _ _) (residueProfileWidth modulus V)
        (residueProfileWidth_pos modulus V hmodulus hV)
        (shiftedUnitProfile_support _ _ (residueProfileWidth_pos modulus V hmodulus hV) ha)
        (by rw [shiftedUnitProfile_mass]; exact hZ) :=
  (coefficientPMF_shiftedUnitProfile _ _ (residueProfileWidth_pos modulus V hmodulus hV)
    (shiftedUnitProfile_support _ _ (residueProfileWidth_pos modulus V hmodulus hV) ha) hZ).symm

theorem residueProfileCenter_le_width {K X : Type*}
    (residue : K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : K × X → ℝ) (hresidue : ∀ z, |(residue z : ℝ)| ≤ V z) (z : K × X) :
    |residueProfileCenter residue modulus z| ≤ residueProfileWidth modulus V z := by
  have hq : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  simp only [residueProfileCenter, residueProfileWidth, abs_div, abs_neg, abs_of_pos hq]
  exact div_le_div_of_nonneg_right (hresidue z) hq.le

namespace BooleanCubeKernel

theorem physicalCube_shifted_comparison {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L κ ρ C : ℝ} {B : ℕ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hC : 1 ≤ C) (hρA : ρ ≤ A) (hρR : ρ ≤ R)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L)
    (hrC : ∀ k, |(root k : ℝ)| ≤ C) (hDC : ∀ i k, |(D i k : ℝ)| ≤ C)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B)
    (a : Option K → ℝ) (ha : ∀ k, |a k| ≤ physicalSpatialInputScale K A R k)
    (hmesh : physicalSpatialMeshCost s C 2 (affineProductProfileLip (Option K) 1) ≤ ρ) :
    let hp := (physicalCube_pivot_control root D s hA hR hL hκ hr hD hminor).1
    ∃ hZ : 0 < shiftedSmoothProductMass a (physicalSpatialInputScale K A R), ∀ v,
      |(∏ i, physicalSpatialOutputScale α A R L i) *
          (((shiftedSmoothProductPMF a (physicalSpatialInputScale K A R)
            (physicalSpatialInputScale_pos K hA hR) hZ).map
              (fun z => physicalCubeCoefficient root D *ᵥ z)) v).toReal -
        coefficientImageMask (physicalCubeCoefficient root D) (physicalSpatialOutputScale α A R L)
          (selectedCoefficientDensity (physicalCubeCoefficient root D) (physicalCubePivotIndex s) hp
            (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L)
            (physicalSpatialInputScale_pos K hA hR) (physicalSpatialOutputScale_pos α hA hR hL)
            (shiftedUnitProfile a (physicalSpatialInputScale K A R))) v| ≤
        physicalSpatialErrorConstant s B κ C 2 1 (affineProductProfileLip (Option K) 1) / ρ := by
  let S := physicalSpatialInputScale K A R
  have hS : ∀ k, 0 < S k := physicalSpatialInputScale_pos K hA hR
  have hs := shiftedUnitProfile_support a S hS ha
  obtain ⟨hZ, he⟩ := physicalCube_full_comparison root D s hA hR hL hκ hρ hC hρA hρR
    hr hD hrC hDC hminor hperiod (shiftedUnitProfile a S) (shiftedUnitProfile_nonneg a S)
    (shiftedUnitProfile_lipschitz a S) (by norm_num) zero_le_one hs
    (shiftedUnitProfile_integral a S) (shiftedUnitProfile_cap a S) hmesh
  have hZ' : 0 < shiftedSmoothProductMass a S := by
    rwa [shiftedUnitProfile_mass] at hZ
  refine ⟨hZ', ?_⟩
  have heq : coefficientPMF (shiftedUnitProfile a S) (shiftedUnitProfile_nonneg a S) S hS hs hZ =
      shiftedSmoothProductPMF a S hS hZ' := coefficientPMF_shiftedUnitProfile a S hS hs hZ'
  dsimp only [S] at he heq
  simpa only [coefficientImagePMF, heq] using he

end BooleanCubeKernel

end Erdos3

end

end OAI
