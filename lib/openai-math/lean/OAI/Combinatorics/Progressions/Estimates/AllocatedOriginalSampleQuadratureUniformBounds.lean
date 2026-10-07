/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.FinsetInj
import Mathlib.Analysis.Calculus.MeanValue
import OAI.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
import OAI.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
import OAI.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_supported :
    ∀ᵐ x ∂allocatedCoefficientSource B U b hR hσ S,
      ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (x j) := by
  let μ := fun j => mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _
  exact ae_all_iff.mpr (fun j => (Measure.quasiMeasurePreserving_eval μ j).ae
    (mixedScalarArrayLaw_support _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _))

theorem allocatedCoefficientSource_ambient_small
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
    ∀ᵐ x ∂allocatedCoefficientSource B U b hR hσ S,
      ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1 / 2 := by
  filter_upwards [allocatedCoefficientSource_supported B U b hR hσ S] with x hx
  intro a
  exact allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmall
    a.1.1 a.1.2 _ (hx a.1.1 a.1.2) a.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "grid" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleRestrictedProfileNoise_short_abs_le (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (e : ActiveProfileCoefficientIndex G B degree grid) :
    |allocatedSampleRestrictedProfileNoise B U basis S grid sample e| ≤ 1 := by
  rcases e with ⟨⟨⟨j, i⟩, ha⟩, e⟩
  have hrows := (mixedArraySupported_iff_rows _ _ _ (sample j)).mp (hs j)
  cases i with
  | inl i =>
    exact allocatedSampleProfileNoise_continuous_bound B U basis hR hσ S sample j i (hrows.1 i) e
  | inr i =>
    exact allocatedSampleProfileNoise_active_integer_bound B U basis hR hσ S sample j i
      (Nat.lt_of_not_ge ha) (hrows.2 i) e

include hR hσ in
theorem allocatedSampleRestrictedProfileNoise_short_ae_abs_le :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
      ∀ e, |allocatedSampleRestrictedProfileNoise B U basis S grid sample e| ≤ 1 := by
  let μ := fun j => mixedScalarArrayLaw (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U basis hR hσ S j) _
  have hs : ∀ᵐ sample ∂Measure.pi μ, ∀ j,
      mixedArraySupported (allocatedLayerCenters B U basis S j)
        (allocatedLayerWidths B U basis S j)
        (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j) :=
    ae_all_iff.mpr (fun j => (Measure.quasiMeasurePreserving_eval μ j).ae
      (mixedScalarArrayLaw_support _ _ (allocatedLayerWidths_pos B U basis hR hσ S j) _))
  exact hs.mono (fun sample hs =>
    allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

def allocatedOriginalSampleInactiveCoefficients
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ :=
  fun a d => (sample (selected a).1).2 (selected a).2 d

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedOriginalSampleInactiveCoefficients_supported
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) :
    ∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
      (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support := by
  intro a d
  exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
    (hs (selected a).1)).2 (selected a).2 d

include hR hσ in
theorem allocatedOriginalSample_forecast_support_ae :
    ∀ᵐ sample ∂allocatedCoefficientSource B U b hR hσ S,
      (∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
        (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support) ∧
      (∀ e, |allocatedSampleRestrictedProfileNoise B U b S
        (allocatedShortAxis (I := I) U b S.value) sample e| ≤ 1) := by
  filter_upwards [allocatedCoefficientSource_supported B U b hR hσ S] with sample hs
  exact ⟨allocatedOriginalSampleInactiveCoefficients_supported B selected U b hR hσ S sample hs,
    allocatedSampleRestrictedProfileNoise_short_abs_le B U b hR hσ S sample hs⟩

theorem allocatedShortAxis_grid (a : LayerSamplerAxis I n)
    (ha : allocatedShortAxis (I := I) U b S.value a) :
    allocatedGridAxis (I := I) U b S.value a := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i => exact False.elim ha
  | inr i =>
    exact ha.trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree j).trans (Nat.le_succ _)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

noncomputable def allocatedOriginalSampleLiftLip : ℝ≥0 := Fintype.card Input * m

include hR hσ in
theorem allocatedOriginalSamplePrincipal_mass (sample : Sample)
    (hr : ∀ e, |noise sample e| ≤ 1) (a : Active) :
    (∑ b, |allocatedOriginalSamplePrincipal B U basis S sample a b|) ≤ 1 := by
  classical
  rw [allocatedOriginalSamplePrincipal_eq_fixedPath B U basis S hR hσ sample,
    allocatedFixedPathPrincipal_eq B short R σ (fun j => (hR j).ne')]
  exact jointSlicedProfilePrincipal_unit_mass degree Subtype.val
    (fun a e => noise sample ⟨a, e⟩) (fun _ _ => hr _) a

include hR hσ in
theorem allocatedOriginalSampleLiftMap_lipschitzOn (sample : Sample)
    (hr : ∀ e, |noise sample e| ≤ 1)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1) :
    LipschitzOnWith (allocatedOriginalSampleLiftLip B U basis S)
      (allocatedOriginalSampleLiftMap B U basis S lower width sample)
      (Metric.closedBall 0 1) := by
  classical
  let c := allocatedOriginalSamplePrincipal B U basis S sample
  have hmap : LipschitzOnWith (allocatedOriginalSampleLiftLip B U basis S)
      (jointSlicedPrincipal c lower width) (Metric.closedBall 0 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => (jointSlicedPrincipal_contDiff c lower width).differentiable (by norm_num) x)
      _ (convex_closedBall 0 1)
    intro x hx
    have hx' : ∀ p, |x p| ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      intro p
      exact (norm_le_pi_norm x p).trans hx
    have he := (jointSlicedPrincipal_c2_bounds c lower width
      (m := m) (fun a => by
        change Fintype.card (Fin (a.val.1.val + 1)) ≤ m
        rw [Fintype.card_fin]
        exact Nat.succ_le_of_lt a.val.1.isLt)
      hwidth zero_le_one
      (allocatedOriginalSamplePrincipal_mass B U basis hR hσ S sample hr) x hx').2.1
    change ‖fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤
      (allocatedOriginalSampleLiftLip B U basis S : ℝ)
    simpa only [allocatedOriginalSampleLiftLip, NNReal.coe_mul, NNReal.coe_natCast, mul_one] using he
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa only [allocatedOriginalSampleLiftMap, dist_add_left] using hmap.dist_le_mul x hx y hy

include hR hσ in
theorem allocatedOriginalSampleLiftMap_supported_lipschitzOn (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1) :
    LipschitzOnWith (allocatedOriginalSampleLiftLip B U basis S)
      (allocatedOriginalSampleLiftMap B U basis S lower width sample)
      (Metric.closedBall 0 1) :=
  allocatedOriginalSampleLiftMap_lipschitzOn B U basis hR hσ S sample
    (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs)
    lower width hwidth

theorem allocatedOriginalSampleLiftMap_affine (sample : Sample)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ) (x : Input → ℝ) :
    allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1) sample
        (fun j => lower j.1 j.2 + width j.1 j.2 * x j) =
      allocatedOriginalSampleLiftMap B U basis S lower width sample x := by
  funext o
  simp only [allocatedOriginalSampleLiftMap_apply, zero_add, one_mul]

include hR hσ in
theorem allocatedOriginalSampleLift_residue_riemann (sample : Sample)
    (hr : ∀ e, |noise sample e| ≤ 1)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℝ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).mean
        (fun z => φ (allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ x, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample x)
        ∂unitBoxMeasure Input| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  classical
  intro lower width K
  let F := allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1) sample
  let project := fun x : Input → Option Empty → ℝ => fun j => x j none
  have hproj : LipschitzWith 1 project := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    exact (dist_le_pi_dist (x j) (y j) none).trans (dist_le_pi_dist x y j)
  have hball : Set.MapsTo project (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact (norm_le_pi_norm (x j) none).trans ((norm_le_pi_norm x j).trans hx)
  have hF := allocatedOriginalSampleLiftMap_lipschitzOn B U basis hR hσ S sample hr
    (fun _ _ => 0) (fun _ _ => 1) (by intro _ _; norm_num)
  have htest : LipschitzOnWith K (fun x => φ (F (project x))) (Metric.closedBall 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      _ ≤ Kφ * dist (F (project x)) (F (project y)) := hφ.dist_le_mul _ _
      _ ≤ Kφ * ((allocatedOriginalSampleLiftLip B U basis S : ℝ) *
          dist (project x) (project y)) :=
        mul_le_mul_of_nonneg_left (hF.dist_le_mul _ (hball hx) _ (hball hy)) Kφ.coe_nonneg
      _ ≤ Kφ * ((allocatedOriginalSampleLiftLip B U basis S : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa using hproj.dist_le_mul x y)
            (allocatedOriginalSampleLiftLip B U basis S).coe_nonneg) Kφ.coe_nonneg
      _ = K * dist x y := by simp only [K, NNReal.coe_mul, mul_assoc]
  have he := progressionTuple_residue_riemann_on_box (fun _ : Input => S.value)
    step H M c (fun _ => S.positive) hstep hH hδ hsubset hdense modulus residue hm hmM
    (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)
    (fun j => by simpa only [Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one]
      using hsmall j) hε hmesh (fun x => φ (F (project x))) htest zero_le_one
    (fun x _ => hφone _)
  have hid (x : Input → Option Empty → ℝ) :
      F (project (affineCubeTuple (fun j => (c j : ℝ) / S.value)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / S.value) x)) =
      allocatedOriginalSampleLiftMap B U basis S lower width sample (project x) := by
    exact allocatedOriginalSampleLiftMap_affine B U basis S sample lower width (project x)
  simp_rw [hid] at he
  have hmeas : Measurable (fun x =>
      φ (allocatedOriginalSampleLiftMap B U basis S lower width sample x)) :=
    hφ.continuous.measurable.comp
      ((allocatedOriginalSampleLiftMap_measurable B U basis S lower width).comp
        (measurable_const.prodMk measurable_id))
  rw [scalarCubeProductMeasure_empty_integral Input _ hmeas] at he
  simpa only [F, project, ite_true, Measure.real, scalarCubeDomain_empty_volume,
    ENNReal.toReal_one, mul_one, div_one] using he

include hR hσ in
theorem allocatedOriginalSampleLift_residue_ae_riemann
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : Sample → (Output → ℝ) → ℝ) {Kφ : ℝ≥0}
    (hφ : ∀ sample, LipschitzWith Kφ (φ sample))
    (hφone : ∀ sample y, ‖φ sample y‖ ≤ 1) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).mean
        (fun z => φ sample (allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ x, φ sample (allocatedOriginalSampleLiftMap B U basis S lower width sample x)
        ∂unitBoxMeasure Input| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  filter_upwards [allocatedSampleRestrictedProfileNoise_short_ae_abs_le B U basis hR hσ S]
    with sample hr
  exact allocatedOriginalSampleLift_residue_riemann B U basis hR hσ S sample hr
    step H M c hstep hH hδ hsubset hdense modulus residue hm hmM hsize hsmall
    hε hmesh (φ sample) (hφ sample) (hφone sample)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

def AllocatedShortIntegerAxis :=
  {a : Σ j : Fin m, Fin (n j) // basisAxisScale (b a.1) a.2 ≤ L ^ (a.1.val + 1)}

noncomputable instance : Fintype (AllocatedShortIntegerAxis U b L) :=
  inferInstanceAs (Fintype {a : Σ j : Fin m, Fin (n j) //
    basisAxisScale (b a.1) a.2 ≤ L ^ (a.1.val + 1)})

def allocatedShortIntegerSelection : AllocatedShortIntegerAxis U b L → Σ j, Fin (n j) :=
  Subtype.val

theorem allocatedShortIntegerSelection_injective :
    Function.Injective (allocatedShortIntegerSelection U b L) :=
  Subtype.val_injective

def allocatedShortIntegerAxisEquiv :
    AllocatedShortIntegerAxis U b L ≃
      {a : LayerSamplerAxis I n // allocatedShortAxis U b L a} where
  toFun a := ⟨⟨a.val.1, Sum.inr a.val.2⟩, a.property⟩
  invFun a := by
    rcases a with ⟨⟨j, i⟩, ha⟩
    cases i with
    | inl i => exact False.elim ha
    | inr i => exact ⟨⟨j, i⟩, ha⟩
  left_inv a := by cases a; rfl
  right_inv a := by
    rcases a with ⟨⟨j, i⟩, ha⟩
    cases i with
    | inl i => exact False.elim ha
    | inr i => rfl

theorem allocatedShortIntegerAxis_card :
    Fintype.card (AllocatedShortIntegerAxis U b L) ≤ ∑ j, n j := by
  calc
    Fintype.card (AllocatedShortIntegerAxis U b L) ≤ Fintype.card (Σ j, Fin (n j)) :=
      Fintype.card_le_of_injective _ (allocatedShortIntegerSelection_injective U b L)
    _ = ∑ j, n j := by simp

theorem allocatedShortIntegerSelection_small (a : AllocatedShortIntegerAxis U b L) :
    basisAxisScale (b (allocatedShortIntegerSelection U b L a).1)
      (allocatedShortIntegerSelection U b L a).2 ≤
      L ^ ((allocatedShortIntegerSelection U b L a).1.val + 1) := a.property

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

include hR hσ in
theorem allocatedOriginalSampleLift_contained_residue_riemann (sample : Sample)
    (hr : ∀ e, |noise sample e| ≤ 1)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℝ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    |(containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).mean
        (fun v => φ (allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value))) -
      ∫ x, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample x)
        ∂unitBoxMeasure Input| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε := by
  classical
  intro lower width K
  let F := allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1) sample
  let f := fun y : JointBlockParameter activeB activeDegree Empty → ℝ =>
    φ (F (fun j : Input => y ⟨j.1, j.2.1, j.2.2, none⟩))
  have hmean := containedProgressionResidueLaw_mean activeB activeDegree (fun _ => S.value)
    H step c (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
    (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j) f
  have hmean' : (containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).mean
        (fun v => φ (F (fun j => (v j none : ℝ) / S.value))) =
      (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) q
        (by have := hH j; omega) (fun _ => q) (residue j) (fun _ => hq) (fun _ => le_rfl)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).mean
        (fun z => φ (F (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) := by
    simpa only [f, principalTupleNormalized, principalTupleIntegers, principalTupleFlatten_apply,
      ite_true, principalResidueWeights] using hmean
  rw [hmean']
  exact allocatedOriginalSampleLift_residue_riemann B U basis hR hσ S sample hr
    step H (fun _ => q) c hstep hH hδ hsubset hdense (fun _ _ => q) residue
    (fun _ _ => hq) (fun _ _ => le_rfl) hsize hsmall hε hmesh φ hφ hφone

theorem allocatedOriginalSampleLift_contained_residue_riemann_of_supported (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) (hq : 0 < q) (residue : Input → Option Empty → ZMod q)
    (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℝ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleLiftLip B U basis S
    |(containedProgressionResidueLaw activeB activeDegree (fun _ => S.value) H step c
        (fun _ => S.positive) (fun j => by have := hH j; omega) hsubset q hq residue
        (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)).mean
        (fun v => φ (allocatedOriginalSampleLiftMap B U basis S (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value))) -
      ∫ x, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample x)
        ∂unitBoxMeasure Input| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (q : ℝ) / H j + K * ε := by
  exact allocatedOriginalSampleLift_contained_residue_riemann B U basis hR hσ S sample
    (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs)
    step H c hstep hH hδ hsubset hdense q hq residue hsize hsmall hε hmesh φ hφ hφone

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))

theorem allocatedOriginalSampleActiveInput_card_le :
    Fintype.card Input ≤ Fintype.card
      (Σ a : LayerSamplerAxis I n, B a × Fin (layerSamplerDegree I n a)) := by
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact Nat.zero_le _

theorem allocatedOriginalSampleLiftLip_le_allAxis :
    allocatedOriginalSampleLiftLip B U basis S ≤
      (Fintype.card (Σ a : LayerSamplerAxis I n,
        B a × Fin (layerSamplerDegree I n a)) : ℝ≥0) * m := by
  unfold allocatedOriginalSampleLiftLip
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast allocatedOriginalSampleActiveInput_card_le B U basis S) zero_le

theorem allocatedOriginalSampleQuadrature_mesh_bound
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) (j : Input) :
    (step j : ℝ) / S.value ≤ 4 / (δ * S.value) := by
  have hs := progression_slice_step_le_inverse_density (c j) S.positive
    (hstep j) (hH j) hδ (hsubset j) (hdense j)
  calc
    (step j : ℝ) / S.value ≤ (4 / δ) / S.value :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = 4 / (δ * S.value) := div_div _ _ _

theorem allocatedOriginalSampleQuadrature_residue_sum_bound
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) (q : ℕ) :
    (∑ j, (q : ℝ) / H j) ≤
      Fintype.card (Σ a : LayerSamplerAxis I n, B a × Fin (layerSamplerDegree I n a)) *
        ((q : ℝ) / (δ * S.value)) := by
  have hpos : 0 < δ * (S.value : ℝ) := mul_pos hδ (by exact_mod_cast S.positive)
  have hH (j : Input) : δ * S.value ≤ (H j : ℝ) := by
    simpa only [card_integerProgressionSupport (c j) (step j) (H j) (hstep j)] using hdense j
  calc
    _ ≤ ∑ _j : Input, (q : ℝ) / (δ * S.value) :=
      Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_left (Nat.cast_nonneg q) hpos (hH j))
    _ = (Fintype.card Input : ℝ) * ((q : ℝ) / (δ * S.value)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast allocatedOriginalSampleActiveInput_card_le B U basis S)
      (div_nonneg (Nat.cast_nonneg _) hpos.le)

end Erdos3.VectorPolynomial

end

end OAI
