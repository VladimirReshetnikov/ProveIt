/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedBooleanSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "Output" => (Σ _e : Row, Unit)

theorem allocatedSlicedOneCube_uniform_density_comparison
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hx : ∀ g, IntegerScalarCube S.value (fun j => (x g j : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun a => (u j a : ℤ)))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hσ : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a δ A η)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |(∫ y, allocatedSlicedAveragedIdealDensity B U basis S hB lower width y *
          φ (fun o => R o.1.2.val.1 * y o)) -
      ∫ p, φ (allocatedSlicedOneCubeEndpointMap B U basis S x u lower width p.1 p.2)
        ∂(unitCoefficientSource Coeff).prod (unitBoxMeasure Endpoint)| ≤ η := by
  let t := slicedPolynomialScale N O N m m 1 1 a δ A η
  have ht := slicedEndpointUniformScale_spec N O m ha hδ A.coe_nonneg hη
  have hsmall := ht.2.2 (Fintype.card Endpoint) (Fintype.card Row) hN hO t (le_of_eq (abs_of_pos ht.1))
  have hb (j : {a // ¬grid a}) : Nonempty (B j.val) :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num : 0 < 4) (hB j))
  let b := fun j : {a // ¬grid a} => Classical.choice (hb j)
  have hcomp := allocatedSlicedOneCubeEndpoint_average_comparison B U basis S x u lower width hwidth
    hx hu b ha hδ hδone hη hprincipal (fun j l => hw j (b j, l)) (fun j l => hl j (b j, l))
    A hA ht.1 hσ hsmall (fun p => φ p.2) (hφ.comp measurable_snd) (fun p => hφone p.2)
  let Φ : (Output → ℝ) → ℝ := fun y => φ (fun o => R o.1.2.val.1 * y o)
  have hΦ : Measurable Φ := hφ.comp (Measurable.of_eval (fun o => measurable_const.mul (measurable_pi_apply o)))
  have hd := allocatedSlicedAveragedIdealDensity_law_probability B U basis S hB lower width ha hδ hprincipal hw hl
  have hm : Measurable (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) :=
    (allocatedSlicedConditionalIdealDensity_measurable B U basis S hB lower width).stronglyMeasurable.integral_prod_left'.measurable
  have he := mappedTest_eq_density
    ((unitCoefficientSource Coeff).prod (unitBoxMeasure Endpoint)) volume
    (fun p => allocatedSlicedNormalizedIdeal B U basis S lower width p.1 p.2)
    (allocatedSlicedNormalizedIdeal_measurable B U basis S lower width)
    (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) hm hd.2.1 hd.1 Φ hΦ
  change (∫ p, φ (allocatedSlicedOneCubeIdeal B U basis S lower width p.1 p.2)
      ∂(unitCoefficientSource Coeff).prod (unitBoxMeasure Endpoint)) =
    ∫ y, allocatedSlicedAveragedIdealDensity B U basis S hB lower width y *
      φ (fun o => R o.1.2.val.1 * y o) at he
  rw [he] at hcomp
  exact hcomp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [decidableB : ∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedSlicedLongJetDensity (y : Endpoint → ℝ) : (Jet → ℝ) → ℝ :=
  allocatedNormalizedLongJetDensity B U basis S x u (fun _ => id) s hA
    (oneCubeSlicedParameter degree grid lower width y)

noncomputable def allocatedSlicedLongJetProxy : (Jet → ℝ) → ℝ :=
  densityMixture (unitBoxMeasure Endpoint) (allocatedSlicedLongJetDensity B U basis S x u s hA lower width)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)

include hR hσ hσ1 in
omit decidableB in
theorem allocatedSlicedLongJetDensity_measurable [∀ a, DecidableEq (B a)] :
    Measurable (Function.uncurry (allocatedSlicedLongJetDensity B U basis S x u s hA lower width)) := by
  have hd := allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u (fun _ => id) s hA hσ1
  have hy := oneCubeSlicedParameter_measurable degree grid lower width
  have hin : Measurable (fun p : (Endpoint → ℝ) × (Jet → ℝ) =>
      (oneCubeSlicedParameter degree grid lower width p.1, p.2)) :=
    (hy.comp measurable_fst).prodMk measurable_snd
  have he := hd.comp hin
  exact he

include hR hσ hσ1 in
omit decidableB in
theorem allocatedSlicedLongJetDensity_probability [∀ a, DecidableEq (B a)] (y : Endpoint → ℝ) :
    (∀ z, 0 ≤ allocatedSlicedLongJetDensity B U basis S x u s hA lower width y z) ∧
    Integrable (allocatedSlicedLongJetDensity B U basis S x u s hA lower width y) ∧
    (∫ z, allocatedSlicedLongJetDensity B U basis S x u s hA lower width y z) = 1 :=
  allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u (fun _ => id) s hA hσ1 _

omit decidableB in
theorem allocatedSlicedLongJetMap_measurable [∀ a, DecidableEq (B a)] :
    Measurable (fun p : (Endpoint → ℝ) × (Coeff → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u (fun _ => id)
        (oneCubeSlicedParameter degree grid lower width p.1) p.2) := by
  have hm := allocatedNormalizedLongJetMap_measurable B U basis S x u
    (O := fun _ => Finset (Fin 1)) (fun _ => id)
  have hy := oneCubeSlicedParameter_measurable degree grid lower width
  have hin : Measurable (fun p : (Endpoint → ℝ) × (Coeff → ℝ) =>
      (oneCubeSlicedParameter degree grid lower width p.1, p.2)) :=
    (hy.comp measurable_fst).prodMk measurable_snd
  have he := hm.comp hin
  exact he

include hR hσ hσ1 in
theorem allocatedSlicedLongJetProxy_image_law :
    ((unitBoxMeasure Endpoint).prod (unitCoefficientSource Coeff)).map
      (fun p => allocatedNormalizedLongJetMap B U basis S x u (fun _ => id)
        (oneCubeSlicedParameter degree grid lower width p.1) p.2) =
      realDensityMeasure volume (allocatedSlicedLongJetProxy B U basis S x u s hA lower width) := by
  have hm := allocatedSlicedLongJetMap_measurable B U basis S x u lower width
  have hd := allocatedSlicedLongJetDensity_measurable B U basis S x u s hA lower width hR hσ hσ1
  have hp := allocatedSlicedLongJetDensity_probability B U basis S x u s hA lower width hR hσ hσ1
  have hlaw (y : Endpoint → ℝ) := allocatedNormalizedLongJetDensity_unit_law
    B U basis hR hσ S x u (fun _ => id) s hA hσ1
      (oneCubeSlicedParameter degree grid lower width y)
  have he := densityMixture_image_law (unitBoxMeasure Endpoint) (unitCoefficientSource Coeff) volume
    _ hm (allocatedSlicedLongJetDensity B U basis S x u s hA lower width) hd hp hlaw
  exact he

include hR hσ hσ1 in
theorem allocatedSlicedLongJetProxy_probability :
    (∀ z, 0 ≤ allocatedSlicedLongJetProxy B U basis S x u s hA lower width z) ∧
    Integrable (allocatedSlicedLongJetProxy B U basis S x u s hA lower width) ∧
    (∫ z, allocatedSlicedLongJetProxy B U basis S x u s hA lower width z) = 1 :=
  densityMixture_probability_density _ _ _
    (allocatedSlicedLongJetDensity_measurable B U basis S x u s hA lower width hR hσ hσ1)
    (Filter.Eventually.of_forall
      (allocatedSlicedLongJetDensity_probability B U basis S x u s hA lower width hR hσ hσ1))

include hR hσ hσ1 in
theorem allocatedSlicedLongJetProxy_endpoint_test
    (φ : ((Σ _e : OneCubeActiveRow grid, Unit) → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ z, allocatedSlicedLongJetProxy B U basis S x u s hA lower width z *
        φ (oneCubeJointJetEndpoints grid z)) =
      ∫ p, φ (allocatedSlicedOneCubeEndpointMap B U basis S x u lower width p.1 p.2)
        ∂(unitCoefficientSource Coeff).prod (unitBoxMeasure Endpoint) := by
  have hm := allocatedSlicedLongJetMap_measurable B U basis S x u lower width
  have hd : Measurable (allocatedSlicedLongJetProxy B U basis S x u s hA lower width) :=
    (allocatedSlicedLongJetDensity_measurable B U basis S x u s hA lower width hR hσ hσ1).stronglyMeasurable.integral_prod_left'.measurable
  have hp := allocatedSlicedLongJetProxy_probability B U basis S x u s hA lower width hR hσ hσ1
  have ht := mappedTest_eq_density ((unitBoxMeasure Endpoint).prod (unitCoefficientSource Coeff)) volume
    _ hm _ hd hp.1
    (allocatedSlicedLongJetProxy_image_law B U basis S x u s hA lower width hR hσ hσ1)
    (φ ∘ oneCubeJointJetEndpoints grid) (hφ.comp (oneCubeJointJetEndpoints_measurable grid))
  exact ht.symm.trans (integral_prod_swap
    (fun p : (Endpoint → ℝ) × (Coeff → ℝ) =>
      φ (allocatedSlicedOneCubeEndpointMap B U basis S x u lower width p.2 p.1))).symm

end Erdos3.VectorPolynomial

end

end OAI
