/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use prod_le_prod' for generic product comparisons; mathematical statements are unchanged. -/
import OAI.Compat.FinsetInj
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
import OAI.Combinatorics.Progressions.Geometry.CanonicalSpatialSupportTwo
import OAI.Combinatorics.Progressions.Sampling.ForecastContinuousRetainedExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S Out : Type*} [Fintype A] [Fintype Out]

theorem exists_forecast_individual_period_factor
    {N : ℕ} [NeZero N] (χ : AddChar (Out → ZMod N) ℂ)
    (e : A → ScalarSiteExpansion S)
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))
    {v O : ℝ} (hq : (orderOf χ : ℝ) ≤ Real.exp v)
    (hperiod : ∀ a, D a ≤ Real.exp O)
    (k : ∀ a, (e a).Term) (s : S) :
    let M := orderOf χ * commonSitePeriod e k
    0 < M ∧ (M : ℝ) ≤ Real.exp (v + Fintype.card A * O) ∧
      ∃ f : (Out → ZMod M) → (A → ZMod M) → (A → ℝ) → ℂ,
        (∀ b z x, ‖f b z x‖ ≤ 1) ∧
        (∀ b z, LipschitzWith (Fintype.card A * L) (f b z)) ∧
        (∀ (b : Out → ℤ) (z : A → ℤ) (x : A → ℝ),
          f (fun i => (b i : ZMod M)) (fun a => (z a : ZMod M)) x =
            star (χ (fun i => (b i : ZMod N))) *
              siteFamilyFactor e k s (fun a => (z a : ZMod ((e a).period (k a)))) x) ∧
        ∀ b z x, (∃ a, H a ≤ |x a|) → f b z x = 0 := by
  intro M
  have hq0 := zmod_character_order_pos χ
  let : NeZero (orderOf χ) := ⟨hq0.ne'⟩
  have hM : 0 < M := Nat.mul_pos hq0 (commonSitePeriod_pos e he k)
  let : NeZero M := ⟨hM.ne'⟩
  have hdq : orderOf χ ∣ M := dvd_mul_right _ _
  have hda (a : A) : (e a).period (k a) ∣ M :=
    (commonSitePeriod_dvd e k a).trans (dvd_mul_left _ _)
  have hcommon : (commonSitePeriod e k : ℝ) ≤ Real.exp (Fintype.card A * O) := by
    simpa only [Real.exp_nat_mul] using commonSitePeriod_le_pow e he hperiod k
  have hMbound : (M : ℝ) ≤ Real.exp (v + Fintype.card A * O) := by
    simpa only [M, Nat.cast_mul, Real.exp_add] using
      mul_le_mul hq hcommon (Nat.cast_nonneg _) (Real.exp_nonneg _)
  obtain ⟨ψ, _, _, _, hψ⟩ := exists_characterOrder_descent χ
  let phase (b : Out → ZMod M) : ℂ :=
    star (ψ (fun i => ZMod.castHom hdq (ZMod (orderOf χ)) (b i)))
  let residues (z : A → ZMod M) : ∀ a, ZMod ((e a).period (k a)) :=
    fun a => ZMod.castHom (hda a) (ZMod ((e a).period (k a))) (z a)
  let f := fun b z x => phase b * siteFamilyFactor e k s (residues z) x
  have hphase (b : Out → ZMod M) : ‖phase b‖ = 1 := by
    simp only [phase, norm_star, AddChar.norm_apply]
  refine ⟨hM, hMbound, f, ?_, ?_, ?_, ?_⟩
  · intro b z x
    dsimp only [f]
    rw [norm_mul, hphase, one_mul]
    exact (siteFamilyFactor_bounds e he k s (residues z)).1 x
  · intro b z
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    change ‖phase b * siteFamilyFactor e k s (residues z) x -
      phase b * siteFamilyFactor e k s (residues z) y‖ ≤ _
    rw [← mul_sub, norm_mul, hphase, one_mul]
    simpa only [dist_eq_norm] using
      (siteFamilyFactor_bounds e he k s (residues z)).2.dist_le_mul x y
  · intro b z x
    dsimp only [f, phase, residues]
    simp only [map_intCast]
    rw [hψ b]
  · intro b z x hx
    dsimp only [f]
    rw [siteFamilyFactor_support e he k s (residues z) x hx, mul_zero]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X J : Type*} [Fintype G] [Fintype X]
  [Fintype J] [DecidableEq J]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)
variable (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hR : ∀ j, R j ≠ 0) (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
  (hprincipal : ∀ j : {a : LayerSamplerAxis I n // ¬P a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
  (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
  (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ) (hr : ∀ e, |r e| ≤ 1)

local notation "ContinuousCoord" => ((Spatial → ℝ) × (Output → ℝ))
local notation "density" => allocatedFixedPathForecastDensity (X := X) B P R σ s root D hp hW hL
  hB lower width r

attribute [local instance] ScalarSiteExpansion.termFinite

include hR ha hδ hprincipal hw hl hr

theorem exists_forecast_smooth_individual_period_factor
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    {Inactive Site Out : Type*} [Fintype Inactive] [Fintype Out]
    {N : ℕ} [NeZero N] (χ : AddChar (Out → ZMod N) ℂ)
    (e : Inactive → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : Inactive → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    {v O : ℝ} (hq : (orderOf χ : ℝ) ≤ Real.exp v)
    (hperiod : ∀ a, Dsite a ≤ Real.exp O)
    (k : ∀ a, (e a).Term) (site : Site) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let K := Real.toNNReal (anisotropicSpatialDensityLip s κ)
    let Acap := allocatedFixedPathLiftRowCap P ha hδ
    let Cs := C ^ Fintype.card X
    let Ks := Fintype.card X * K * C ^ Fintype.card X
    let Cl := ∏ j, Acap j
    let Kl := (∏ j, (Acap j + 1)) * ∑ j, Acap j * (2 * Acap j)
    let H : ℝ := Cs * Cl + 1
    let M := orderOf χ * commonSitePeriod e k
    0 < M ∧ (M : ℝ) ≤ Real.exp (v + Fintype.card Inactive * O) ∧
      ∃ f : (Out → ZMod M) → (Inactive → ZMod M) →
          (ContinuousCoord × (Inactive → ℝ)) → ℂ,
        (∀ b z y, ‖f b z y‖ ≤ 1) ∧
        (∀ b z, LipschitzWith
          (Cl * Ks + Cs * Kl + Fintype.card Inactive * Lsite) (f b z)) ∧
        (∀ (b : Out → ℤ) (z : Inactive → ℤ) (y : ContinuousCoord) (xi : Inactive → ℝ),
          (density y : ℂ) * star (χ (fun i => (b i : ZMod N))) *
            siteFamilyFactor e k site (fun a => (z a : ZMod ((e a).period (k a)))) xi =
          (H : ℂ) * f (fun i => (b i : ZMod M)) (fun a => (z a : ZMod M)) (y, xi)) ∧
        (∀ b z y, (∃ a, Hsite a ≤ |y.2 a|) → f b z y = 0) ∧
        (∀ b z y, density y.1 = 0 → f b z y = 0) := by
  intro C K Acap Cs Ks Cl Kl H M
  have hb := allocatedFixedPathForecastDensity_normalized_bounds (X := X)
    B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
    hκ hroot hminor
  obtain ⟨hM, hMb, g, hg, hgL, hgeval, hgsupport⟩ :=
    exists_forecast_individual_period_factor χ e he hq hperiod k site
  let F := fun y : ContinuousCoord × (Inactive → ℝ) => (density y.1 : ℂ) / (H : ℂ)
  have hF : ∀ y : ContinuousCoord × (Inactive → ℝ), ‖F y‖ ≤ 1 := fun y => hb.1 y.1
  have hFL : LipschitzWith (Cl * Ks + Cs * Kl) F := by
    simpa only [Function.comp_def, mul_one] using hb.2.1.comp
      (LipschitzWith.prod_fst (α := ContinuousCoord) (β := Inactive → ℝ))
  let f := fun b z (y : ContinuousCoord × (Inactive → ℝ)) => F y * g b z y.2
  refine ⟨hM, hMb, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro b z y
    dsimp only [f]
    rw [norm_mul]
    exact (mul_le_mul (hF y) (hg b z y.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro b z
    have hGL : LipschitzWith (Fintype.card Inactive * Lsite)
        (fun y : ContinuousCoord × (Inactive → ℝ) => g b z y.2) := by
      simpa only [Function.comp_def, mul_one] using (hgL b z).comp
        (LipschitzWith.prod_snd (α := ContinuousCoord) (β := Inactive → ℝ))
    simpa only [one_mul, add_comm] using
      lipschitz_mul_of_bounds F (fun y => g b z y.2) hFL hGL
        (Bf := 1) (Bg := 1) hF (fun y => hg b z y.2)
  · intro b z y xi
    change (density y : ℂ) * star (χ (fun i => (b i : ZMod N))) *
      siteFamilyFactor e k site (fun a => (z a : ZMod ((e a).period (k a)))) xi =
      (H : ℂ) * (F (y, xi) * g (fun i => (b i : ZMod M)) (fun a => (z a : ZMod M)) xi)
    rw [hgeval]
    have hnorm : (density y : ℂ) = (H : ℂ) * F (y, xi) := hb.2.2 y
    rw [hnorm]
    ring
  · intro b z y hy
    change F y * g b z y.2 = 0
    rw [hgsupport b z y.2 hy, mul_zero]
  · intro b z y hy
    change ((density y.1 : ℂ) / (H : ℂ)) * g b z y.2 = 0
    rw [hy, Complex.ofReal_zero, zero_div, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "amin" => unitProfilePrincipalLowerBound B
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)

noncomputable def allocatedOriginalSampleForecastDensity (sample : Sample) : Domain → ℝ :=
  allocatedFixedPathForecastDensity (X := X) B short R σ s root D hp hW hL
    hB lower width (noise sample)

noncomputable def allocatedOriginalForecastCap : ℝ≥0 :=
  (Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1) ^ Fintype.card X *
    ∏ a, allocatedFixedPathLiftRowCap short hamin hδ a

noncomputable def allocatedOriginalForecastLip : ℝ≥0 :=
  (∏ a, allocatedFixedPathLiftRowCap short hamin hδ a) *
    (Fintype.card X * Real.toNNReal (anisotropicSpatialDensityLip s 1) *
      (Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1) ^ Fintype.card X) +
  (Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1) ^ Fintype.card X *
    ((∏ a, (allocatedFixedPathLiftRowCap short hamin hδ a + 1)) *
      ∑ a, allocatedFixedPathLiftRowCap short hamin hδ a *
        (2 * allocatedFixedPathLiftRowCap short hamin hδ a))

local notation "density" => allocatedOriginalSampleForecastDensity (X := X)
  B U basis S s root D hp hW hL hB lower width
local notation "cap" => allocatedOriginalForecastCap (X := X) B U basis S s hδ
local notation "lip" => allocatedOriginalForecastLip (X := X) B U basis S s hδ

noncomputable def allocatedOriginalSampleNormalizedForecast (sample : Sample) (z : Domain) : ℂ :=
  (density sample z : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ)

variable (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

include hR hσ hδ hw hl in
theorem allocatedOriginalSampleForecastDensity_ae_probability :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
      (∀ z, 0 ≤ density sample z) ∧ Integrable (density sample) ∧
        (∫ z, density sample z) = 1 := by
  filter_upwards [allocatedSampleRestrictedProfileNoise_short_ae_abs_le B U basis hR hσ S]
    with sample hr
  exact allocatedFixedPathForecastDensity_probability_data B short R σ s root D hp hW hL
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr

include hR hσ hδ hw hl in
theorem allocatedOriginalSampleForecastDensity_ae_bounds
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
      (∀ z, density sample z ∈ Set.Icc (0 : ℝ) cap) ∧ LipschitzWith lip (density sample) := by
  filter_upwards [allocatedSampleRestrictedProfileNoise_short_ae_abs_le B U basis hR hσ S]
    with sample hr
  exact allocatedFixedPathForecastDensity_cap_lipschitz B short R σ s root D hp hW hL
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
    zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])

include hR hσ hδ hw hl in
theorem allocatedOriginalSampleNormalizedForecast_ae_bounds
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
      (∀ z, ‖allocatedOriginalSampleNormalizedForecast (X := X)
        B U basis S s root D hp hW hL hB lower width hδ sample z‖ ≤ 1) ∧
      LipschitzWith lip (allocatedOriginalSampleNormalizedForecast (X := X)
        B U basis S s root D hp hW hL hB lower width hδ sample) ∧
      (∀ z, (density sample z : ℂ) = (((cap : ℝ) + 1 : ℝ) : ℂ) *
        allocatedOriginalSampleNormalizedForecast (X := X)
          B U basis S s root D hp hW hL hB lower width hδ sample z) := by
  filter_upwards [allocatedSampleRestrictedProfileNoise_short_ae_abs_le B U basis hR hσ S]
    with sample hr
  exact allocatedFixedPathForecastDensity_normalized_bounds B short R σ s root D hp hW hL
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
    zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])

include hR hσ hδ hw hl in
theorem allocatedOriginalSampleForecastDensity_ae_support
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
      (∀ z : Domain, 3 < ‖z‖ → density sample z = 0) ∧ HasCompactSupport (density sample) := by
  filter_upwards [allocatedSampleRestrictedProfileNoise_short_ae_abs_le B U basis hR hσ S]
    with sample hr
  exact ⟨allocatedFixedPathForecastDensity_zero_off_ball B short R σ s root D hp hW hL
      (fun j => (hR j).ne') hB lower width hamin hδ
      (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr hroot hwidth,
    allocatedFixedPathForecastDensity_compact B short R σ s root D hp hW hL
      (fun j => (hR j).ne') hB lower width hamin hδ
      (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr hroot hwidth⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedForecastAllAxisRowCap {δ : ℝ} (hδ : 0 < δ)
    (a : LayerSamplerAxis I n) : ℝ≥0 :=
  allocatedFixedPathLiftRowCap (fun _ : LayerSamplerAxis I n => False)
    (unitProfilePrincipalLowerBound_pos B) hδ ⟨a, not_false⟩

noncomputable def allocatedForecastAllAxisLiftCap {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  ∏ a, (allocatedForecastAllAxisRowCap B hδ a + 1)

noncomputable def allocatedForecastAllAxisLiftLip {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  allocatedForecastAllAxisLiftCap B hδ *
    ∑ a, allocatedForecastAllAxisRowCap B hδ a * (2 * allocatedForecastAllAxisRowCap B hδ a)

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable {δ : ℝ} (hδ : 0 < δ)

omit [DecidablePred P] in
theorem allocatedFixedPathLiftRowCap_eq_allAxis (a : {a // ¬P a}) :
    allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a =
      allocatedForecastAllAxisRowCap B hδ a.val := rfl

theorem allocatedFixedPathLift_prod_add_one_le_allAxis :
    (∏ a, (allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a + 1)) ≤
      allocatedForecastAllAxisLiftCap B hδ := by
  apply Finset.prod_le_prod_of_injOn Subtype.val
      (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact le_add_of_nonneg_left zero_le

theorem allocatedFixedPathLift_prod_le_allAxis :
    (∏ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a) ≤
      allocatedForecastAllAxisLiftCap B hδ := by
  calc
    _ ≤ ∏ a, (allocatedFixedPathLiftRowCap P
        (unitProfilePrincipalLowerBound_pos B) hδ a + 1) :=
      Finset.prod_le_prod' (fun _ _ => le_add_of_nonneg_right zero_le_one)
    _ ≤ _ := allocatedFixedPathLift_prod_add_one_le_allAxis B P hδ

theorem allocatedFixedPathLift_sum_lip_le_allAxis :
    (∑ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a *
      (2 * allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a)) ≤
    ∑ a, allocatedForecastAllAxisRowCap B hδ a * (2 * allocatedForecastAllAxisRowCap B hδ a) := by
  apply Finset.sum_le_sum_of_injOn Subtype.val
      (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact zero_le

theorem allocatedFixedPathLift_lip_le_allAxis :
    (∏ a, (allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a + 1)) *
      (∑ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a *
        (2 * allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a)) ≤
      allocatedForecastAllAxisLiftLip B hδ :=
  mul_le_mul' (allocatedFixedPathLift_prod_add_one_le_allAxis B P hδ)
    (allocatedFixedPathLift_sum_lip_le_allAxis B P hδ)

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp)

noncomputable def allocatedForecastAllAxisCap : ℝ≥0 :=
  (Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1) ^ Fintype.card X *
    allocatedForecastAllAxisLiftCap B hδ

noncomputable def allocatedForecastAllAxisLip : ℝ≥0 :=
  allocatedForecastAllAxisLiftCap B hδ *
    (Fintype.card X * Real.toNNReal (anisotropicSpatialDensityLip s 1) *
      (Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1) ^ Fintype.card X) +
  (Real.toNNReal (anisotropicSpatialDensityCap s 1) + 1) ^ Fintype.card X *
    allocatedForecastAllAxisLiftLip B hδ

variable {G : Type*} [Fintype G] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

omit [DecidableEq Zsp] [∀ a, DecidableEq (B a)] in
theorem allocatedOriginalForecastCap_le_allAxis :
    allocatedOriginalForecastCap (X := X) B U basis S s hδ ≤
      allocatedForecastAllAxisCap (X := X) B hδ s := by
  exact mul_le_mul' le_rfl (allocatedFixedPathLift_prod_le_allAxis B
    (allocatedShortAxis U basis S.value) hδ)

omit [DecidableEq Zsp] [∀ a, DecidableEq (B a)] in
theorem allocatedOriginalForecastLip_le_allAxis :
    allocatedOriginalForecastLip (X := X) B U basis S s hδ ≤
      allocatedForecastAllAxisLip (X := X) B hδ s := by
  exact add_le_add
    (mul_le_mul' (allocatedFixedPathLift_prod_le_allAxis B
      (allocatedShortAxis U basis S.value) hδ) le_rfl)
    (mul_le_mul' le_rfl (allocatedFixedPathLift_lip_le_allAxis B
      (allocatedShortAxis U basis S.value) hδ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "amin" => unitProfilePrincipalLowerBound B
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

omit [∀ index, DecidableEq (B index)] in
theorem allocatedOriginalSampleForecastDensity_coordinate_bound_two
    [∀ index, DecidableEq (B index)]
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (sample : Sample) (v : Domain)
    (hne : allocatedOriginalSampleForecastDensity (X := X) B U basis S s root D hp hW hL
      hB lower width sample v ≠ 0) :
    ∀ i : X, |v.1 ⟨i, .inl ()⟩| ≤ 2 := by
  apply canonicalZeroSpatialJointDensity_coordinate_bound_two s root D hp hW hL hroot v.1
  exact (mul_ne_zero_iff.mp hne).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

local notation "density" => allocatedOriginalSampleForecastDensity (X := X)
  B U basis S s root D hp hW hL hB lower width
local notation "cap" => allocatedOriginalForecastCap (X := X) B U basis S s hδ
local notation "lip" => allocatedOriginalForecastLip (X := X) B U basis S s hδ

attribute [local instance] ScalarSiteExpansion.termFinite

include hR hσ hw hl in

theorem exists_allocatedOriginalSampleForecastAtom
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    {Inactive Site Out : Type*} [Fintype Inactive] [Fintype Out]
    {N : ℕ} [NeZero N] (χ : AddChar (Out → ZMod N) ℂ)
    (e : Inactive → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : Inactive → ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    {v O : ℝ} (hq : (orderOf χ : ℝ) ≤ Real.exp v)
    (hperiod : ∀ a, Dsite a ≤ Real.exp O)
    (k : ∀ a, (e a).Term) (site : Site) :
    let M := orderOf χ * commonSitePeriod e k
    0 < M ∧ (M : ℝ) ≤ Real.exp (v + Fintype.card Inactive * O) ∧
      ∃ f : (Out → ZMod M) → (Inactive → ZMod M) →
          (Domain × (Inactive → ℝ)) → ℂ,
        (∀ b z y, ‖f b z y‖ ≤ 1) ∧
        (∀ b z, LipschitzWith (lip + Fintype.card Inactive * Lsite) (f b z)) ∧
        (∀ (b : Out → ℤ) (z : Inactive → ℤ) (y : Domain) (xi : Inactive → ℝ),
          (density sample y : ℂ) * star (χ (fun i => (b i : ZMod N))) *
            siteFamilyFactor e k site (fun a => (z a : ZMod ((e a).period (k a)))) xi =
          (((cap : ℝ) + 1 : ℝ) : ℂ) *
            f (fun i => (b i : ZMod M)) (fun a => (z a : ZMod M)) (y, xi)) ∧
        (∀ b z y, (∃ a, Hsite a ≤ |y.2 a|) → f b z y = 0) ∧
        (∀ b z y, density sample y.1 = 0 → f b z y = 0) := by
  exact exists_forecast_smooth_individual_period_factor (X := X)
    B short R σ s root D hp hW hL (fun j => (hR j).ne') hB lower width
    hamin hδ (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample)
    (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs)
    zero_lt_one hroot (by simp only [Matrix.det_isEmpty, abs_one, le_refl])
    χ e he hq hperiod k site

include hR hσ hw hl in

theorem exists_allocatedOriginalSampleForecastAtom_supported
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {Inactive Site Out : Type*} [Fintype Inactive] [Fintype Out]
    {N : ℕ} [NeZero N] (χ : AddChar (Out → ZMod N) ℂ)
    (e : Inactive → ScalarSiteExpansion Site)
    {Tsite Dsite Csite : Inactive → ℝ} {Hsite : ℝ} {Lsite : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite Hsite)
    {v O : ℝ} (hq : (orderOf χ : ℝ) ≤ Real.exp v)
    (hperiod : ∀ a, Dsite a ≤ Real.exp O)
    (k : ∀ a, (e a).Term) (site : Site) :
    let M := orderOf χ * commonSitePeriod e k
    0 < M ∧ (M : ℝ) ≤ Real.exp (v + Fintype.card Inactive * O) ∧
      ∃ f : (Out → ZMod M) → (Inactive → ZMod M) →
          (Domain × (Inactive → ℝ)) → ℂ,
        (∀ b z y, ‖f b z y‖ ≤ 1) ∧
        (∀ b z, LipschitzWith (lip + Fintype.card Inactive * Lsite) (f b z)) ∧
        (∀ (b : Out → ℤ) (z : Inactive → ℤ) (y : Domain) (xi : Inactive → ℝ),
          (density sample y : ℂ) * star (χ (fun i => (b i : ZMod N))) *
            siteFamilyFactor e k site (fun a => (z a : ZMod ((e a).period (k a)))) xi =
          (((cap : ℝ) + 1 : ℝ) : ℂ) *
            f (fun i => (b i : ZMod M)) (fun a => (z a : ZMod M)) (y, xi)) ∧
        (∀ b z y, max 3 Hsite < ‖y‖ → f b z y = 0) ∧
        (∀ b z, HasCompactSupport (f b z)) := by
  have hroot' : ∀ j, |(root j : ℝ)| ≤ 1 + W := by
    intro j
    have hj : |(root j : ℝ)| ≤ ∑ j, |(root j : ℝ)| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (root i : ℝ)) (Finset.mem_univ j)
    linarith
  obtain ⟨hM, hMb, f, hf, hfL, hfeval, hsite, hdensity⟩ :=
    exists_allocatedOriginalSampleForecastAtom (X := X) B U basis hR hσ S
      s root D hp hW hL hB lower width hδ hw hl sample hs hroot'
      χ e he hq hperiod k site
  refine ⟨hM, hMb, f, hf, hfL, hfeval, ?_⟩
  have hzero : ∀ b z y, max 3 Hsite < ‖y‖ → f b z y = 0 := by
    intro b z y hy
    have hor : max 3 Hsite < ‖y.1‖ ∨ max 3 Hsite < ‖y.2‖ := by
      simpa only [Prod.norm_def, lt_max_iff] using hy
    rcases hor with hcontinuous | hinactive
    · apply hdensity b z y
      exact allocatedFixedPathForecastDensity_zero_off_ball (X := X)
        B short R σ s root D hp hW hL (fun j => (hR j).ne') hB lower width
        hamin hδ (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample)
        (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs)
        hroot hwidth y.1 ((le_max_left 3 Hsite).trans_lt hcontinuous)
    · apply hsite b z y
      by_contra hn
      have hb : ‖y.2‖ ≤ max 3 Hsite := by
        apply (pi_norm_le_iff_of_nonneg
          ((by norm_num : (0 : ℝ) ≤ 3).trans (le_max_left _ _))).mpr
        intro a
        rw [Real.norm_eq_abs]
        exact (lt_of_not_ge (fun h => hn ⟨a, h⟩)).le.trans (le_max_right _ _)
      exact (not_le.mpr hinactive) hb
  refine ⟨hzero, ?_⟩
  intro b z
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : Domain × (Inactive → ℝ)) (max 3 Hsite))
  intro y hy
  exact hzero b z y
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy)

end Erdos3.VectorPolynomial

end

end OAI
