import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedProxyQuadrature
import OAI.Combinatorics.Progressions.Geometry.AllocatedSlicedIdealSupport
import OAI.Combinatorics.Progressions.Geometry.OneCubeSliceSupport
import OAI.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

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
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedSlicedPhysicalEndpointIdeal : (Output → ℝ) → ℝ :=
  diagonalDensityTransport (fun o => R o.1.2.val.1) (fun o => (hR o.1.2.val.1).ne')
    (allocatedSlicedAveragedIdealDensity B U basis S hB lower width)

noncomputable def allocatedSlicedPhysicalJetIdeal : (Jet → ℝ) → ℝ :=
  fun z => allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width (oneCubeJointJetEndpoints grid z)

theorem allocatedSlicedPhysicalEndpointIdeal_measurable :
    Measurable (allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width) := by
  have hm : Measurable (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) :=
    (allocatedSlicedConditionalIdealDensity_measurable B U basis S hB lower width).stronglyMeasurable.integral_prod_left'.measurable
  exact linearDensityPullback_measurable _ hm

theorem allocatedSlicedPhysicalJetIdeal_measurable :
    Measurable (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width) :=
  (allocatedSlicedPhysicalEndpointIdeal_measurable B U basis S hR hB lower width).comp
    (oneCubeJointJetEndpoints_measurable grid)

theorem allocatedSlicedPhysicalEndpointIdeal_probability {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p) :
    (∀ z, 0 ≤ allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width z) ∧
      Integrable (allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width) ∧
      (∫ z, allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width z) = 1 := by
  have hp := (allocatedSlicedAveragedIdealDensity_law_probability B U basis S hB lower width
    ha hδ hprincipal hw hl).2
  refine ⟨linearDensityPullback_nonneg _ hp.1, linearDensityPullback_integrable _ hp.2.1, ?_⟩
  change (∫ z, linearDensityPullback _ _ z) = 1
  rw [linearDensityPullback_integral, hp.2.2]

theorem allocatedSlicedPhysicalJetIdeal_probability {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p) :
    (∀ z, 0 ≤ allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z) ∧
      Integrable (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width) ∧
      (∫ z, allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z) = 1 := by
  have hp := allocatedSlicedPhysicalEndpointIdeal_probability B U basis S hR hB lower width ha hδ hprincipal hw hl
  have hv := oneCubeJointJetEndpoints_volume grid
  exact ⟨fun z => hp.1 _, hv.integrable_comp_of_integrable hp.2.1,
    (hv.integral_comp (by rw [oneCubeJointJetEndpoints_equiv]; exact MeasurableEquiv.measurableEmbedding _) _).trans hp.2.2⟩

omit [∀ a, DecidableEq (B a)] in
theorem allocatedSlicedPhysicalJetIdeal_test [∀ a, DecidableEq (B a)]
    (φ : (Jet → ℝ) → ℝ) :
    (∫ z, allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z * φ z) =
      ∫ y, allocatedSlicedAveragedIdealDensity B U basis S hB lower width y *
        φ ((oneCubeJetEndpointEquiv {a // ¬grid a}).symm (fun o => R o.1.2.val.1 * y o)) := by
  let e := oneCubeJetEndpointEquiv {a // ¬grid a}
  have hv := oneCubeJetEndpointEquiv_volume {a // ¬grid a}
  have hi := hv.integral_comp e.measurableEmbedding
    (fun y => allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width y * φ (e.symm y))
  simp only [e, MeasurableEquiv.symm_apply_apply] at hi
  change (∫ z, allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width (oneCubeJointJetEndpoints grid z) * φ z) = _
  rw [oneCubeJointJetEndpoints_equiv, hi]
  exact diagonalDensityTransport_test_integral _ _ _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

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
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "Jac" => ‖(∏ o : Output, R (Sigma.fst (Subtype.val (Prod.snd (Sigma.fst o)))))⁻¹‖₊

theorem allocatedSlicedPhysicalJetIdeal_uniform_bounds
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    {a δ P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (M : ℝ≥0) (hInv : ∀ j, (R j)⁻¹ ≤ M) :
    let C : ℝ≥0 := ⟨Real.exp (slicedJointDensityLogBudget O m P), Real.exp_nonneg _⟩
    (∀ z, |allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z| ≤ (Jac : ℝ) * C) ∧
      LipschitzWith ((Jac * (C * M)) * 2)
        (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width) := by
  intro C
  have hb := allocatedSlicedAveragedIdealDensity_uniform_bounds B U basis S O hO hB lower width
    ha hδ hP haP hδP hprincipal hw hl
  have hc (y) : |allocatedSlicedAveragedIdealDensity B U basis S hB lower width y| ≤ (C : ℝ) := by
    rw [abs_of_nonneg (hb.1 y).1]
    exact (hb.1 y).2
  constructor
  · intro z
    have he := diagonalDensityTransport_bound (fun o : Output => R o.1.2.val.1)
      (fun o => (hR o.1.2.val.1).ne') _ hc (oneCubeJointJetEndpoints grid z)
    convert he using 1 <;> rfl
  · have he := diagonalDensityTransport_lipschitz (fun o : Output => R o.1.2.val.1)
      (fun o => (hR o.1.2.val.1).ne') _ hb.2
      (fun o => (abs_of_pos (inv_pos.mpr (hR o.1.2.val.1))).le.trans (hInv o.1.2.val.1))
    have hcomp := he.comp (oneCubeJetEndpointEquiv_lipschitz {a // ¬grid a})
    change LipschitzWith _ (allocatedSlicedPhysicalEndpointIdeal B U basis S hR hB lower width ∘ oneCubeJointJetEndpoints grid)
    rw [oneCubeJointJetEndpoints_equiv]
    exact hcomp

theorem allocatedSlicedPhysicalJetIdeal_zero_off_ball
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (M : ℝ≥0) (hRM : ∀ j, R j ≤ M) (z : Jet → ℝ) (hz : 4 * (M : ℝ) < ‖z‖) :
    allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z = 0 := by
  let e := oneCubeJetEndpointEquiv {a // ¬grid a}
  let w : Output → ℝ := fun o => e z o / R o.1.2.val.1
  have hrec : (fun o : Output => R o.1.2.val.1 * w o) = e z := by
    funext o
    exact mul_div_cancel₀ _ (hR o.1.2.val.1).ne'
  have hs := coordinateScale_lipschitz (fun o : Output => R o.1.2.val.1)
    (fun o => (abs_of_pos (hR o.1.2.val.1)).le.trans (hRM o.1.2.val.1))
  have hnorm : ‖e z‖ ≤ (M : ℝ) * ‖w‖ := by
    have hh := hs.dist_le_mul w 0
    simp only [Pi.zero_apply, mul_zero] at hh
    change dist (fun o => R o.1.2.val.1 * w o) 0 ≤ (M : ℝ) * dist w 0 at hh
    simpa only [hrec, dist_zero_right] using hh
  have hw2 : 2 < ‖w‖ := by
    have he := oneCubeJet_norm_le {a // ¬grid a} z
    change ‖z‖ ≤ 2 * ‖e z‖ at he
    nlinarith [M.coe_nonneg]
  unfold allocatedSlicedPhysicalJetIdeal allocatedSlicedPhysicalEndpointIdeal
  rw [diagonalDensityTransport_eq, oneCubeJointJetEndpoints_equiv]
  have he := allocatedSlicedAveragedIdealDensity_zero_off_ball B U basis S hB lower width hwidth
    ha hδ hprincipal hw hl w hw2
  change |∏ o : Output, R o.1.2.val.1|⁻¹ * allocatedSlicedAveragedIdealDensity B U basis S hB lower width w = 0
  rw [he, mul_zero]

end Erdos3.VectorPolynomial

end

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

theorem allocatedSlicedLongJetProxy_uniform_l1
    (hR : ∀ j, 0 < R j) (hσpos : ∀ j, 0 < σ j)
    (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
    (hKernel : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
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
    : (∫ z, |allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z -
        allocatedSlicedLongJetProxy B U basis S x u s hKernel lower width z|) ≤ η := by
  have ht := slicedEndpointUniformScale_spec N O m ha hδ A.coe_nonneg hη
  have hσ1 (j) : σ j ≤ 1 := (le_abs_self _).trans ((hσ j).trans ht.2.1)
  have hi := allocatedSlicedPhysicalJetIdeal_probability B U basis S hR hB lower width ha hδ hprincipal hw hl
  have hp := allocatedSlicedLongJetProxy_probability B U basis S x u s hKernel lower width hR hσpos hσ1
  have hmi := allocatedSlicedPhysicalJetIdeal_measurable B U basis S hR hB lower width
  have hmp : Measurable (allocatedSlicedLongJetProxy B U basis S x u s hKernel lower width) :=
    (allocatedSlicedLongJetDensity_measurable B U basis S x u s hKernel lower width hR hσpos hσ1).stronglyMeasurable.integral_prod_left'.measurable
  apply density_l1_le_of_bounded_tests volume _ _ hmi hmp hi.2.1 hp.2.1
  intro φ hφ hφone
  let e := oneCubeJetEndpointEquiv {a // ¬grid a}
  let ψ : (Output → ℝ) → ℝ := φ ∘ e.symm
  have hψ : Measurable ψ := hφ.comp e.symm.measurable
  have he := allocatedSlicedOneCube_uniform_density_comparison B U basis S x u
    N O hN hO hB lower width hwidth hx hu ha hδ hδone hη hprincipal hw hl A hA hσ
    ψ hψ (fun y => hφone _)
  rw [allocatedSlicedPhysicalJetIdeal_test]
  have htest := allocatedSlicedLongJetProxy_endpoint_test B U basis S x u s hKernel lower width hR hσpos hσ1 ψ hψ
  have hcompose : (fun z => ψ (oneCubeJointJetEndpoints grid z)) = φ := by
    funext z
    simp only [ψ, e, Function.comp_apply, oneCubeJointJetEndpoints_equiv, MeasurableEquiv.symm_apply_apply]
  simp_rw [show ∀ z, ψ (oneCubeJointJetEndpoints grid z) = φ z from congrFun hcompose] at htest
  rw [htest]
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal BigOperators

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
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [∀ a, DecidableEq (B a)] in
theorem allocatedSlicedPhysicalJetIdeal_normalized_sites [∀ a, DecidableEq (B a)]
    (v : Finset (Fin 1) → LayerSamplerAxis I n → ℝ) :
    (∏ o : Output, R o.1.2.val.1) * allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
      (booleanSiteJets (fun _ : {a // ¬grid a} => id) (fun t a => R a.val.1 * v t a.val)) =
      allocatedSlicedAveragedIdealDensity B U basis S hB lower width (oneCubeSiteRestriction grid v) := by
  have hprod : 0 < ∏ o : Output, R o.1.2.val.1 := Finset.prod_pos (fun o _ => hR _)
  change (∏ o : Output, R o.1.2.val.1) *
    diagonalDensityTransport (fun o : Output => R o.1.2.val.1) (fun o => (hR _).ne')
      (allocatedSlicedAveragedIdealDensity B U basis S hB lower width)
      (oneCubeJointJetEndpoints grid
        (booleanSiteJets (fun _ : {a // ¬grid a} => id) (fun t a => R a.val.1 * v t a.val))) = _
  rw [oneCubeJointJetEndpoints_booleanSiteJets grid (fun t a => R a.1 * v t a),
    diagonalDensityTransport_eq, abs_of_pos hprod]
  have hcancel : (fun o : Output => oneCubeSiteRestriction grid (fun t a => R a.1 * v t a) o /
      R o.1.2.val.1) = oneCubeSiteRestriction grid v := by
    funext o
    exact mul_div_cancel_left₀ _ (hR _).ne'
  rw [hcancel, ← mul_assoc, mul_inv_cancel₀ hprod.ne', one_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

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
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable [DecidableEq G]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) id (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)

include hR hσ hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedSlicedLongJetProxy_output_bounds (hσ1 : ∀ j, σ j ≤ 1) :
    (∀ z, allocatedSlicedLongJetProxy B U basis S x u s hA lower width z ∈ Set.Icc (0 : ℝ) cap) ∧
      LipschitzWith lip (allocatedSlicedLongJetProxy B U basis S x u s hA lower width) := by
  have hm := allocatedSlicedLongJetDensity_measurable B U basis S x u s hA lower width hR hσ hσ1
  have hb (y : Endpoint → ℝ) := allocatedNormalizedLongJetDensity_output_bounds
    B U basis hR hσ S x (fun _ => id) s hA hM hi hP hMP hRP hRi hσi hcount u hσ1
      (oneCubeSlicedParameter degree grid lower width y)
  exact densityMixture_uniform_bound (unitBoxMeasure Endpoint)
    (allocatedSlicedLongJetDensity B U basis S x u s hA lower width) cap lip
    (fun z => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hb)

include hR hσ hM hi hP hMP hRP hRi hσi hcount in
omit [∀ a, DecidableEq (B a)] in
theorem allocatedSlicedLongJetProxy_zero_off_ball [∀ a, DecidableEq (B a)]
    (hσ1 : ∀ j, σ j ≤ 1)
    (hw : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (z : Jet → ℝ) (hz : radius < ‖z‖) :
    allocatedSlicedLongJetProxy B U basis S x u s hA lower width z = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [oneCubeSlicedParameter_ae_norm_le degree grid lower width hw] with y hy
  exact allocatedNormalizedLongJetDensity_zero_off_ball B U basis hR hσ S x (fun _ => id) s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1 (oneCubeSlicedParameter degree grid lower width y) hy z hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal BigOperators

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
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [∀ a, DecidableEq (B a)] in
theorem allocatedSlicedPhysicalJetIdeal_normalized_coordinates [∀ a, DecidableEq (B a)]
    (z : Jet → ℝ) :
    (∏ o : Output, R o.1.2.val.1) * allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z =
      allocatedSlicedAveragedIdealDensity B U basis S hB lower width
        (oneCubeSiteRestriction grid (oneCubeNormalizedSites grid (fun a => R a.1) z)) := by
  have hprod : 0 < ∏ o : Output, R o.1.2.val.1 := Finset.prod_pos (fun o _ => hR _)
  rw [oneCubeNormalizedSites_restriction]
  change (∏ o : Output, R o.1.2.val.1) *
    diagonalDensityTransport (fun o : Output => R o.1.2.val.1) (fun o => (hR _).ne')
      (allocatedSlicedAveragedIdealDensity B U basis S hB lower width)
      (oneCubeJointJetEndpoints grid z) = _
  rw [diagonalDensityTransport_eq, abs_of_pos hprod, ← mul_assoc, mul_inv_cancel₀ hprod.ne', one_mul]

theorem allocatedSlicedPhysicalJetIdeal_cutoff
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ d, |v d| ≤ 2) → χ v = 1) (z : Jet → ℝ) :
    (∏ t : Finset (Fin 1), χ (oneCubeNormalizedSites grid (fun a => R a.1) z t)) *
      allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z =
      allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z := by
  by_cases hz : allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width z = 0
  · simp only [hz, mul_zero]
  · have hnorm : ‖fun o : Output => oneCubeJointJetEndpoints grid z o / R o.1.2.val.1‖ ≤ 2 := by
      by_contra! hn
      have he := allocatedSlicedAveragedIdealDensity_zero_off_ball B U basis S hB lower width
        hwidth ha hδ hprincipal hw hl _ hn
      apply hz
      change diagonalDensityTransport _ _ _ _ = 0
      rw [diagonalDensityTransport_eq, he, mul_zero]
    have hsites := oneCubeNormalizedSites_bound grid (fun a => R a.1) z (by norm_num) hnorm
    have hprod : (∏ t : Finset (Fin 1), χ (oneCubeNormalizedSites grid (fun a => R a.1) z t)) = 1 :=
      Finset.prod_eq_one (fun t _ => hone _ (hsites t))
    rw [hprod, one_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

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
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))

local notation "Output" => (Σ _e : OneCubeActiveRow grid, Unit)

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "Jac" => ‖(∏ o : Output, R (Sigma.fst (Subtype.val (Prod.snd (Sigma.fst o)))))⁻¹‖₊

theorem allocatedSlicedLongProfile_integrable
    (O : ℕ) (hO : Fintype.card (OneCubeActiveRow grid) ≤ O)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (hRbound : ∀ j, R j ≤ Real.exp P) (hInv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (Finset (Fin 1)) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue j) z ≤ Cmask) :
    Integrable (allocatedLongProfileDensity B U basis S x (fun _ => id) modulus residue
      (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width))
      (allocatedLongJetReference B U basis S (fun _ => Finset (Fin 1))) := by
  have hb := allocatedSlicedPhysicalJetIdeal_uniform_bounds B U basis S hR hB lower width
    O hO ha hδ hP haP hδP hprincipal hw hl (NNReal.mk (Real.exp P) (Real.exp_nonneg _)) hInv
  have hs := allocatedSlicedPhysicalJetIdeal_zero_off_ball B U basis S hR hB lower width hwidth
    ha hδ hprincipal hw hl (NNReal.mk (Real.exp P) (Real.exp_nonneg _)) hRbound
  exact allocatedLongProfileDensity_integrable B U basis S x (fun _ => id) modulus residue
    _ (allocatedSlicedPhysicalJetIdeal_measurable B U basis S hR hB lower width)
    (mul_nonneg (by norm_num) (Real.exp_nonneg _)) hs hCmask
    (mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)) hb.1 hmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedLongJetProxy_residue_l1 (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option (Fin 1) → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card (Fin 1) + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant (Fin 1) * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) :
    let Δ := fun z : Jet → ℝ => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights (Fin 1) (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u (fun _ => id) s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) (Fin 1)
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedSlicedLongJetProxy B U basis S x u s hA
        (fun a p => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩)
        (fun a p => (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩) z
    Integrable Δ ∧ (∫ z, |Δ z|) ≤
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet := by
  intro Δ
  let weights := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights (Fin 1) (H j) (M j)
    (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))
  let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
  let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
    (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
  let F := fun (v : ∀ j, IntegerScalarCubeBox (Fin 1) (H j)) =>
    principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) (Fin 1)
      (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)
  let proxy := allocatedSlicedLongJetProxy B U basis S x u s hA lower width
  let density := allocatedNormalizedLongJetDensity B U basis S x u (fun _ => id) s hA
  let radius := Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)
  have hw (a) (p) : |lower a p| + |width a p| ≤ 1 :=
    (progression_slice_endpoint_geometry (c ⟨a,p⟩) (hL _) (hstep _) (hH _) hδ
      (hsubset _) (hdense _)).2.2.1
  have hF (v) (hv : 0 < weights.weight v) : ‖F v‖ ≤ 1 := by
    apply (principalTupleFlatten_norm_apply_le _ _ _ _).trans
    apply progressionTuple_norm_le L step H c hH (fun j => hw j.1 j.2) v
    intro j
    exact scalarCubeResidueWeights_cube_support (Fin 1) (H j) (M j) (by have := hH j; omega)
      (modulus j) (residue j) (hm j) (hmM j) (hsize j) (v j)
      (FiniteProbabilityWeights.pi_weight_pos_component _ v hv j)
  have hs (z : Jet → ℝ) (hz : radius < ‖z‖) : Δ z = 0 := by
    have hp : proxy z = 0 := allocatedSlicedLongJetProxy_zero_off_ball B U basis S x u s hA
      lower width hR hσ hMk hi hP hMkP hRP hRi hσi hcount hσ1 hw z hz
    have hd : weights.mean (fun v => density (F v) z) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      by_cases hv : weights.weight v = 0
      · simp only [hv, zero_mul]
      · have hf := allocatedNormalizedLongJetDensity_zero_off_ball B U basis hR hσ S x
          (fun _ => id) s hA hMk hi hP hMkP hRP hRi hσi hcount u hσ1 (F v)
          (hF v (lt_of_le_of_ne (weights.nonneg v) (Ne.symm hv))) z hz
        exact mul_eq_zero_of_right _ hf
    exact sub_eq_zero.mpr (hd.trans hp.symm)
  have hint : Integrable (fun z => weights.mean (fun v => density (F v) z)) := by
    apply integrable_finsetSum
    intro v _
    exact ((allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u
      (fun _ => id) s hA hσ1 (F v)).2.1).const_mul (weights.weight v)
  have hip := (allocatedSlicedLongJetProxy_probability B U basis S x u s hA
    lower width hR hσ hσ1).2.1
  refine ⟨hint.sub hip, ?_⟩
  apply integral_norm_le_box Δ (Real.exp_nonneg _) hs
  intro z _
  exact allocatedSlicedLongJetProxy_residue_error B U basis hR hσ S x u s hA hMk hi hP hMkP
    hRP hRi hσi hcount hσ1 L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedDiscreteIdeal_l1
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option (Fin 1) → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card (Fin 1) + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant (Fin 1) * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun i => (u j i : ℤ)))
    {a η : ℝ} (ha : 0 < a) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (A : ℝ≥0) (hTransition : LipschitzWith A Real.smoothTransition)
    (hσsmall : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a (δ / 2) A η) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
    let discrete := fun z =>
      (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights (Fin 1) (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u (fun _ => id) s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) (Fin 1)
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
    (∫ z, |ideal z - discrete z|) ≤ η +
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet := by
  intro lower width ideal discrete
  let proxy := allocatedSlicedLongJetProxy B U basis S x u s hA lower width
  have hδhalf : 0 < δ / 2 := half_pos hδ
  have hδhalf1 : δ / 2 ≤ 1 := by linarith
  have ht := slicedEndpointUniformScale_spec N O m ha hδhalf A.coe_nonneg hη
  have hσ1 (j) : σ j ≤ 1 := (le_abs_self _).trans ((hσsmall j).trans ht.2.1)
  have hg (a) (p) := progression_slice_endpoint_geometry (c ⟨a,p⟩)
    (hL _) (hstep _) (hH _) hδ (hsubset _) (hdense _)
  have hw (a) (p) : |lower a p| + |width a p| ≤ 1 := (hg a p).2.2.1
  have hl (a) (p) : 0 ≤ lower a p := (hg a p).1
  have hwδ (a) (p) : δ / 2 ≤ width a p := (hg a p).2.1
  have hcont := allocatedSlicedLongJetProxy_uniform_l1 B U basis S x u hR hσ s hA
    N O hN hO hB lower width hw hx hu ha hδhalf hδhalf1 hη hprincipal hwδ hl A hTransition hσsmall
  have hdisc := allocatedSlicedLongJetProxy_residue_l1 B U basis hR hσ S x u s hA hMk hi hP hMkP
    hRP hRi hσi hcount hσ1 L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh
  have hi := (allocatedSlicedPhysicalJetIdeal_probability B U basis S hR hB lower width
    ha hδhalf hprincipal hwδ hl).2.1
  have hp := (allocatedSlicedLongJetProxy_probability B U basis S x u s hA lower width hR hσ hσ1).2.1
  have hdiff : Integrable (fun z => ideal z - proxy z) := hi.sub hp
  calc
    _ ≤ ∫ z, (|ideal z - proxy z| + |discrete z - proxy z|) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (hdiff.abs.add hdisc.1.abs)
      apply Filter.Eventually.of_forall
      intro z
      change |ideal z - discrete z| ≤ |ideal z - proxy z| + |discrete z - proxy z|
      simpa only [abs_sub_comm (proxy z) (discrete z)] using
        abs_sub_le (ideal z) (proxy z) (discrete z)
    _ = (∫ z, |ideal z - proxy z|) + ∫ z, |discrete z - proxy z| :=
      integral_add hdiff.abs hdisc.1.abs
    _ ≤ _ := add_le_add hcont hdisc.2

end Erdos3.VectorPolynomial

end

end OAI
