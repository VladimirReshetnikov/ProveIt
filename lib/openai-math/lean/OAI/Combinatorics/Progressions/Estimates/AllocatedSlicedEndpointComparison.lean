/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Probability.OneCubeSlicedSourceLaw

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

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "Output" => (Σ _e : Row, Unit)
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))
local notation "extra" => (fun g a => (g, a) : G → Option (Fin 1) → G × Option (Fin 1))

noncomputable def allocatedSlicedOneCubeIdeal
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) (y : Endpoint → ℝ) (o : Output) : ℝ :=
  R o.1.2.val.1 *
    (jointSlicedProfileShift degree axis (fun _ => 1 / 4) (fun e j => r ⟨e.2, j⟩) o +
      jointSlicedPrincipal
        (jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B)) (fun e j => r ⟨e.2, j⟩))
        (fun e => lower e.2) (fun e => width e.2) y o)

variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

theorem allocatedSlicedOneCubeIdeal_measurable
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ) :
    Measurable (fun p : (Coeff → ℝ) × (Endpoint → ℝ) =>
      allocatedSlicedOneCubeIdeal B U basis S lower width p.1 p.2) := by
  let _ : ∀ axisIndex, DecidableEq (B axisIndex) := inferInstance
  unfold allocatedSlicedOneCubeIdeal jointSlicedProfileShift jointSlicedPrincipal sigmaAxisSampler
    principalSliceSingleton principalSliceValue jointSlicedProfilePrincipal
  fun_prop

theorem allocatedSlicedOneCubeEndpointMap_measurable
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ) :
    Measurable (fun p : (Coeff → ℝ) × (Endpoint → ℝ) =>
      allocatedSlicedOneCubeEndpointMap B U basis S x u lower width p.1 p.2) := by
  let _ : ∀ axisIndex, DecidableEq (B axisIndex) := inferInstance
  have hj := allocatedNormalizedLongJetMap_measurable B U basis S x u
    (O := fun _ => Finset (Fin 1)) (fun _ => id)
  have hinput : Measurable (fun p : (Coeff → ℝ) × (Endpoint → ℝ) =>
      (oneCubeSlicedParameter degree grid lower width p.2, p.1)) :=
    ((oneCubeSlicedParameter_measurable degree grid lower width).comp measurable_snd).prodMk measurable_fst
  have hjet := hj.comp hinput
  have hout := (oneCubeJointJetEndpoints_measurable grid).comp hjet
  exact hout

theorem allocatedSlicedOneCubeEndpointMap_test_law
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) :
    mappedTest (unitBoxMeasure Endpoint)
        (allocatedSlicedOneCubeEndpointMap B U basis S x u lower width r) φ =
      mappedTest
        ((jointBooleanSource (B := fun a : {a // ¬grid a} => B a.val) (α := Fin 1)
          (fun a => degree a.val)).map (oneCubeJointShiftScale degree grid lower width))
        (fun y => oneCubeJointJetEndpoints grid (allocatedNormalizedLongJetMap B U basis S x u (fun _ => id) y r)) φ := by
  let _ : ∀ axisIndex, DecidableEq (B axisIndex) := inferInstance
  have hj := allocatedNormalizedLongJetMap_measurable B U basis S x u
    (O := fun _ => Finset (Fin 1)) (fun _ => id)
  have hr : Measurable (fun y : PrincipalAxisParameter (B := B) (h := degree) (α := Fin 1)
      (fun a => ¬grid a) → ℝ => allocatedNormalizedLongJetMap B U basis S x u (fun _ => id) y r) :=
    hj.comp (f := fun y => (y, r)) (measurable_id.prodMk measurable_const)
  have hm := (oneCubeJointJetEndpoints_measurable grid).comp hr
  rw [← oneCubeSlicedParameter_source_law degree grid lower width]
  symm
  exact integral_map (oneCubeSlicedParameter_measurable degree grid lower width).aemeasurable
    (hφ.comp hm).aestronglyMeasurable

theorem allocatedSlicedProfileFrozenEndpoints_abs_le
    (hx : ∀ g, IntegerScalarCube S.value (fun j => (x g j : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun a => (u j a : ℤ))) :
    ∀ β k, |oneCubeProfileFrozenEndpoints degree grid extra
      (allocatedProfileFrozenNoise B U basis S x u) β k| ≤ 1 := by
  let _ : ∀ axisIndex, DecidableEq (B axisIndex) := inferInstance
  intro β k
  rcases k with g | ⟨d, b, v⟩
  · have hb := (integerScalarCube_iff_normalized S.positive _).mp (hx g) (oneCubeVertex β)
    change |scalarCubeValue (fun j => ((x g j : ℤ) : ℝ) / S.value) (oneCubeVertex β)| ≤ 1
    rw [abs_of_nonneg hb.1]
    exact hb.2.le
  · by_cases hd : grid d
    · have hb := (integerScalarCube_iff_normalized
        (allocatedPrincipalSides_pos B U basis S ⟨d, b, v⟩) _).mp
          (hu ⟨⟨d, hd⟩, b, v⟩) (oneCubeVertex β)
      have hb' : |scalarCubeValue
          (fun j => ((u ⟨⟨d, hd⟩, b, v⟩ j : ℤ) : ℝ) /
            allocatedPrincipalSides B U basis S ⟨d, b, v⟩) (oneCubeVertex β)| ≤ 1 := by
        rw [abs_of_nonneg hb.1]
        exact hb.2.le
      simpa only [oneCubeProfileFrozenEndpoints, allocatedProfileFrozenNoise, normalizedCubeTuple,
        partitionedPrincipalInput, hd, ↓reduceDIte, Sum.elim_inl, Sum.elim_inr,
        principalTupleNormalized, principalTupleIntegers, principalAxisLength, scalarCubeValue] using hb'
    · simp only [oneCubeProfileFrozenEndpoints, allocatedProfileFrozenNoise, normalizedCubeTuple,
        partitionedPrincipalInput, hd, ↓reduceDIte, Sum.elim_inr, mul_zero, Finset.sum_const_zero,
        abs_zero, zero_le_one]

theorem allocatedSlicedOneCubeEndpoint_comparison
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hfrozen : ∀ β k, |oneCubeProfileFrozenEndpoints degree grid extra
      (allocatedProfileFrozenNoise B U basis S x u) β k| ≤ 1)
    (b : ∀ a : {a // ¬grid a}, B a.val)
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j l, δ ≤ width j (b j, l)) (hlower : ∀ j l, 0 ≤ lower j (b j, l))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {t : ℝ} (ht : 0 < t) (hσ : ∀ j, |σ j| ≤ t)
    (hsmall : |t| * polynomialMassC2Budget (Fintype.card Endpoint) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Endpoint) (Fintype.card Row) m 1 a δ A η)
    (r : Coeff → ℝ) (hr : ∀ j, |r j| ≤ 1)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure Endpoint) (allocatedSlicedOneCubeIdeal B U basis S lower width r) φ -
      mappedTest (unitBoxMeasure Endpoint)
        (allocatedSlicedOneCubeEndpointMap B U basis S x u lower width r) φ| ≤ η := by
  let z := allocatedSlicedEndpointNoise B U basis S x u t r
  let coeff := oneCubeProfileEndpointNoise degree grid z
  let ξ := oneCubeProfileSubstitution degree grid lower width (oneCubeProfileFrozenEndpoints degree grid extra z)
  have hz : ∀ j, |z j| ≤ 1 := profileNoiseWithActive_abs_le degree grid _ _
    (allocatedProfileFrozenNoise_abs_le B U basis S x u)
    (activeTailRescale_abs_le degree grid _ (allocatedTailRatio_abs_le ht hσ) r hr)
  have hcoeff : ∀ e j, |coeff e j| ≤ 1 := fun e j => hz (.inr ⟨e.2.val, j⟩)
  have hfrozen' : ∀ β k, |oneCubeProfileFrozenEndpoints degree grid extra z β k| ≤ 1 := hfrozen
  let Φ : (Output → ℝ) → ℝ := fun v => φ (fun o => R o.1.2.val.1 * v o)
  have hΦ : Measurable Φ := hφ.comp (Measurable.of_eval (fun o => measurable_const.mul (measurable_pi_apply o)))
  have hcomp := jointSlicedProfileValue_unit_comparison degree axis
    (fun _ => Nat.zero_lt_succ _) (fun e => Nat.succ_le_of_lt e.2.val.1.isLt)
    (fun _ => 1 / 4) coeff hcoeff ξ
    (oneCubeProfileSubstitution_degree degree grid lower width _)
    (oneCubeProfileSubstitution_mass degree grid lower width hwidth _ hfrozen')
    (fun e => lower e.2) (fun e => width e.2)
    (oneCubeProfileSubstitution_principal degree grid lower width _)
    (fun e => hwidth e.2) (fun e => b e.2) (fun e => ⟨0, Nat.zero_lt_succ _⟩)
    ha hδ hδone hη (fun e => hprincipal e.2) (fun e => hw e.2)
    (fun e j _ => hlower e.2 j) A hA t hsmall Φ hΦ (fun v => hφone _)
  have hc : jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B)) coeff =
      jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B)) (fun e j => r ⟨e.2, j⟩) := by
    funext e j
    simp only [jointSlicedProfilePrincipal, coeff, oneCubeProfileEndpointNoise, z,
      allocatedSlicedEndpointNoise, profileNoiseWithActive_active, activeTailRescale_principal]
  have hs : jointSlicedProfileShift degree axis (fun _ => 1 / 4) coeff =
      jointSlicedProfileShift degree axis (fun _ => 1 / 4) (fun e j => r ⟨e.2, j⟩) := by
    funext o
    simp only [jointSlicedProfileShift, coeff, oneCubeProfileEndpointNoise, z,
      allocatedSlicedEndpointNoise, profileNoiseWithActive_active, activeTailRescale_constant]
  rw [hc, hs] at hcomp
  have hmap (y : Endpoint → ℝ) : allocatedSlicedOneCubeEndpointMap B U basis S x u lower width r y =
      fun o => R o.1.2.val.1 * jointSlicedProfileValue degree axis (fun _ => 1 / 4)
        (unitProfilePrincipalSize (B := B)) (unitProfileTailSize (G := G) (B := B) degree) coeff ξ t y o := by
    rw [allocatedSlicedOneCubeEndpointMap_eq B U basis S x u lower width r ht.ne']
    exact jointSlicedProfileValue_unit_scale degree axis (fun a => R a.1) coeff ξ t y
  simp_rw [mappedTest, hmap]
  exact hcomp

theorem allocatedSlicedOneCubeEndpoint_average_comparison
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hx : ∀ g, IntegerScalarCube S.value (fun j => (x g j : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun a => (u j a : ℤ)))
    (b : ∀ a : {a // ¬grid a}, B a.val)
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j l, δ ≤ width j (b j, l)) (hlower : ∀ j l, 0 ≤ lower j (b j, l))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {t : ℝ} (ht : 0 < t) (hσ : ∀ j, |σ j| ≤ t)
    (hsmall : |t| * polynomialMassC2Budget (Fintype.card Endpoint) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Endpoint) (Fintype.card Row) m 1 a δ A η)
    (φ : (Coeff → ℝ) × (Output → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |(∫ p, φ (p.1, allocatedSlicedOneCubeIdeal B U basis S lower width p.1 p.2)
        ∂(unitCoefficientSource Coeff).prod (unitBoxMeasure Endpoint)) -
      ∫ p, φ (p.1, allocatedSlicedOneCubeEndpointMap B U basis S x u lower width p.1 p.2)
        ∂(unitCoefficientSource Coeff).prod (unitBoxMeasure Endpoint)| ≤ η := by
  apply product_image_comparison_of_ae_fiber_bounds (unitCoefficientSource Coeff) (unitBoxMeasure Endpoint)
    _ _ (allocatedSlicedOneCubeIdeal_measurable B U basis S lower width)
    (allocatedSlicedOneCubeEndpointMap_measurable B U basis S x u lower width) _ φ hφ hφone
  filter_upwards [unitCoefficientSource_abs_le Coeff] with r hr
  intro f hf hfbound
  exact allocatedSlicedOneCubeEndpoint_comparison B U basis S x u lower width hwidth
    (allocatedSlicedProfileFrozenEndpoints_abs_le B U basis S x u hx hu) b ha hδ hδone hη
    hprincipal hw hlower A hA ht hσ hsmall r hr f hf hfbound

end Erdos3.VectorPolynomial

end

end OAI
