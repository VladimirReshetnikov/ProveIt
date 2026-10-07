/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.AllocatedFixedPathLiftSupport
import OAI.Combinatorics.Progressions.Probability.CanonicalZeroSpatialDensity
import OAI.Combinatorics.Progressions.Sampling.ForecastContinuousNormalization

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w uR

variable {R : Type uR} {A : Type u} {S : Type v}
variable [Fintype R] [Fintype A] [Fintype S]
variable (e : R → A → ScalarSiteExpansion.{v,w} S)

noncomputable def forecastSiteMixtureCoefficient (c : R → ℂ)
    (t : Σ r, ∀ a, (e r a).Term) : ℂ :=
  c t.1 * siteFamilyCoefficient (e t.1) t.2

theorem forecastSiteMixture_expansion (c : R → ℂ)
    (y : S → A → ℤ) (x : S → A → ℝ) :
    (∑ r, c r * siteFamilyEval (e r) y x) =
      ∑ t : Σ r, ∀ a, (e r a).Term,
        forecastSiteMixtureCoefficient e c t * ∏ s,
          siteFamilyFactor (e t.1) t.2 s
            (fun a => (y s a : ZMod ((e t.1 a).period (t.2 a)))) (x s) := by
  simp only [Fintype.sum_sigma, forecastSiteMixtureCoefficient, siteFamilyEval,
    Finset.mul_sum, mul_assoc]

omit [Fintype S] in
theorem forecastSiteMixture_coefficient_mass
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (hC : ∀ a, 0 ≤ C a) (c : R → ℂ) {M : ℝ}
    (hc : (∑ r, ‖c r‖) ≤ M) :
    (∑ t : Σ r, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e c t‖) ≤
      M * ∏ a, C a := by
  exact sigma_sum_coefficient_norm_le c (fun r => siteFamilyCoefficient (e r))
    (Finset.prod_nonneg (fun a _ => hC a)) hc
    (fun r => siteFamily_coefficient_le (e r) (he r))

theorem forecastResidueWeight_mass (w : R → ℝ) (a : R → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (ha : ∀ r, ‖a r‖ ≤ 1) :
    (∑ r, ‖(w r : ℂ) * a r‖) ≤ 1 := by
  apply le_trans (Finset.sum_le_sum (fun r _ => ?_)) hmass
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw r)]
  exact mul_le_of_le_one_right (hw r) (ha r)

omit [Fintype S] in
theorem forecastSiteMixture_weighted_mass
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (hC : ∀ a, 0 ≤ C a) (w : R → ℝ) (a : R → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (ha : ∀ r, ‖a r‖ ≤ 1) :
    (∑ t : Σ r, ∀ a, (e r a).Term,
      ‖forecastSiteMixtureCoefficient e (fun r => (w r : ℂ) * a r) t‖) ≤ ∏ a, C a := by
  simpa only [one_mul] using forecastSiteMixture_coefficient_mass e he hC
    (fun r => (w r : ℂ) * a r) (forecastResidueWeight_mass w a hw hmass ha)

omit [Fintype S] in

theorem forecastSiteMixture_inactive_mass
    {Ω Z : Type*} [Fintype Ω]
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (hC : ∀ a, 0 ≤ C a)
    (p : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z) (residue : Ω → R)
    (a : R → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1) (z : Z) :
    (∑ t : Σ r, ∀ a, (e r a).Term,
      ‖forecastSiteMixtureCoefficient e (fun r =>
        (p.fiberMean residue r (fun i => if gridPoint i = z then 1 else 0) : ℂ) * a r) t‖) ≤
      p.fiberMean gridPoint z (fun _ => 1) * ∏ a, C a :=
  forecastSiteMixture_coefficient_mass e he hC _
    (inactiveResidueCoefficient_mass_le p gridPoint residue a ha z)

theorem forecastSiteMixture_error (c μ : R → ℂ)
    (y : S → A → ℤ) (x : S → A → ℝ) {M δ : ℝ}
    (hδ : 0 ≤ δ) (hc : (∑ r, ‖c r‖) ≤ M)
    (he : ∀ r, ‖μ r - siteFamilyEval (e r) y x‖ ≤ δ) :
    ‖(∑ r, c r * μ r) - (∑ r, c r * siteFamilyEval (e r) y x)‖ ≤ M * δ := by
  rw [forecastSiteMixture_expansion]
  exact sigma_sum_approximation_error c μ (fun r => siteFamilyCoefficient (e r))
    (fun r k => ∏ s, siteFamilyFactor (e r) k s
      (fun a => (y s a : ZMod ((e r a).period (k a)))) (x s)) hδ hc he

theorem forecastSiteMixture_weighted_error (w : R → ℝ) (a μ : R → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (ha : ∀ r, ‖a r‖ ≤ 1)
    (y : S → A → ℤ) (x : S → A → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (he : ∀ r, ‖μ r - siteFamilyEval (e r) y x‖ ≤ δ) :
    ‖(∑ r, (w r : ℂ) * a r * μ r) -
      (∑ r, (w r : ℂ) * a r * siteFamilyEval (e r) y x)‖ ≤ δ := by
  simpa only [one_mul] using forecastSiteMixture_error e
    (fun r => (w r : ℂ) * a r) μ y x hδ (forecastResidueWeight_mass w a hw hmass ha) he

theorem forecastSiteMixture_twisted_error (c μ : R → ℂ)
    (y : S → A → ℤ) (x : S → A → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (∑ r, ‖c r‖) ≤ 1)
    (he : ∀ r, ‖μ r - siteFamilyEval (e r) y x‖ ≤ δ)
    (G χ : S → ℂ) (hG : ∀ s, ‖G s‖ ≤ 1) (hχ : ∀ s, ‖χ s‖ ≤ 1) :
    ‖((∑ r, c r * μ r) * ∏ s, χ s * G s) -
      ((∑ r, c r * siteFamilyEval (e r) y x) * ∏ s, χ s * G s)‖ ≤ δ := by
  rw [← sub_mul, norm_mul]
  have hprod : ‖∏ s, χ s * G s‖ ≤ 1 := by
    rw [norm_prod]
    apply (Finset.prod_le_prod₀ (fun s _ => norm_nonneg _) (fun s _ => ?_)).trans_eq
      Finset.prod_const_one
    rw [norm_mul]
    exact (mul_le_mul (hχ s) (hG s) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact (mul_le_of_le_one_right (norm_nonneg _) hprod).trans
    (by simpa only [one_mul] using forecastSiteMixture_error e c μ y x hδ hc he)

theorem forecastSiteMixture_twisted_expansion (c : R → ℂ)
    (y : S → A → ℤ) (x : S → A → ℝ) (G χ : S → ℂ) :
    (∑ r, c r * siteFamilyEval (e r) y x) * (∏ s, χ s * G s) =
      ∑ t : Σ r, ∀ a, (e r a).Term,
        forecastSiteMixtureCoefficient e c t * ∏ s,
          (χ s * G s) * siteFamilyFactor (e t.1) t.2 s
            (fun a => (y s a : ZMod ((e t.1 a).period (t.2 a)))) (x s) := by
  rw [forecastSiteMixture_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.prod_mul_distrib]
  ring

omit [Fintype R] [Fintype S] in

theorem forecastSiteMixture_factor_bounds
    {T D C H : A → ℝ} {L K : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (t : Σ r, ∀ a, (e r a).Term) (s : S)
    (r : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (G : (A → ℝ) → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1) (hGL : LipschitzWith K G)
    (χ : ℂ) (hχ : ‖χ‖ ≤ 1) :
    (∀ x, ‖(χ * G x) * siteFamilyFactor (e t.1) t.2 s r x‖ ≤ 1) ∧
      LipschitzWith (K + Fintype.card A * L)
        (fun x => (χ * G x) * siteFamilyFactor (e t.1) t.2 s r x) := by
  obtain ⟨hb, hL⟩ := siteFamilyFactor_bounds (e t.1) (he t.1) t.2 s r
  have hχG : ∀ x, ‖χ * G x‖ ≤ 1 := by
    intro x
    rw [norm_mul]
    exact (mul_le_mul hχ (hG x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hχGL : LipschitzWith K (fun x => χ * G x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hχ).trans
      (by simpa only [dist_eq_norm] using hGL.dist_le_mul x y)
  refine ⟨fun x => ?_, ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul (hχG x) (hb x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simpa only [one_mul, add_comm] using
      lipschitz_mul_of_bounds (fun x => χ * G x) (siteFamilyFactor (e t.1) t.2 s r)
        hχGL hL (Bf := 1) (Bg := 1) hχG hb

omit [Fintype R] [Fintype S] in
theorem forecastSiteMixture_factor_support
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (t : Σ r, ∀ a, (e r a).Term) (s : S)
    (r : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (G : (A → ℝ) → ℂ) (χ : ℂ) (x : A → ℝ)
    (hx : ∃ a, H a ≤ |x a|) :
    (χ * G x) * siteFamilyFactor (e t.1) t.2 s r x = 0 := by
  rw [siteFamilyFactor_support (e t.1) (he t.1) t.2 s r x hx, mul_zero]

omit [Fintype R] [Fintype S] in

theorem forecastSiteMixture_factor_comp_bounds
    {X : Type*} [PseudoMetricSpace X]
    {T D C H : A → ℝ} {L K Kcoord : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (t : Σ r, ∀ a, (e r a).Term) (s : S)
    (r : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (G : X → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1) (hGL : LipschitzWith K G)
    (coord : X → A → ℝ) (hcoord : LipschitzWith Kcoord coord)
    (χ : ℂ) (hχ : ‖χ‖ ≤ 1) :
    (∀ x, ‖(χ * G x) * siteFamilyFactor (e t.1) t.2 s r (coord x)‖ ≤ 1) ∧
      LipschitzWith (K + (Fintype.card A * L) * Kcoord)
        (fun x => (χ * G x) * siteFamilyFactor (e t.1) t.2 s r (coord x)) := by
  obtain ⟨hb, hL⟩ := siteFamilyFactor_bounds (e t.1) (he t.1) t.2 s r
  have hχG : ∀ x, ‖χ * G x‖ ≤ 1 := by
    intro x
    rw [norm_mul]
    exact (mul_le_mul hχ (hG x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hχGL : LipschitzWith K (fun x => χ * G x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hχ).trans
      (by simpa only [dist_eq_norm] using hGL.dist_le_mul x y)
  refine ⟨fun x => ?_, ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul (hχG x) (hb (coord x)) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simpa only [one_mul, add_comm, Function.comp_def] using
      lipschitz_mul_of_bounds (fun x => χ * G x)
        (fun x => siteFamilyFactor (e t.1) t.2 s r (coord x))
        hχGL (hL.comp hcoord) (Bf := 1) (Bg := 1) hχG (fun x => hb (coord x))

omit [Fintype R] [Fintype S] in
theorem forecastSiteMixture_factor_comp_support
    {X : Type*} {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (t : Σ r, ∀ a, (e r a).Term) (s : S)
    (r : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (G : X → ℂ) (coord : X → A → ℝ) (χ : ℂ) (x : X)
    (hx : ∃ a, H a ≤ |coord x a|) :
    (χ * G x) * siteFamilyFactor (e t.1) t.2 s r (coord x) = 0 := by
  rw [siteFamilyFactor_support (e t.1) (he t.1) t.2 s r (coord x) hx, mul_zero]

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

noncomputable def allocatedFixedPathForecastDensity :
    ((Spatial → ℝ) × (Output → ℝ)) → ℝ :=
  binaryDensity (canonicalZeroSpatialJointDensity s root D hp hW hL)
    (allocatedFixedPathLiftDensity B P R σ hB lower width r)

local notation "f" => canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL
local notation "g" => allocatedFixedPathLiftDensity B P R σ hB lower width r
local notation "density" => allocatedFixedPathForecastDensity (X := X) B P R σ s root D hp hW hL
  hB lower width r

include hR ha hδ hprincipal hw hl hr

theorem allocatedFixedPathForecastDensity_probability_data :
    (∀ y, 0 ≤ density y) ∧ Integrable density ∧ (∫ y, density y) = 1 := by
  have hf := canonicalZeroSpatialJointDensity_probability_data (X := X) s root D hp hW hL
  have hg := allocatedFixedPathLiftDensity_law_probability B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  refine ⟨fun y => mul_nonneg (hf.1 y.1) (hg.2.1 y.2),
    binaryDensity_integrable hf.2.1 hg.2.2.1, ?_⟩
  change (∫ y, binaryDensity f g y ∂volume.prod volume) = 1
  rw [binaryDensity_mass, hf.2.2, hg.2.2.2, one_mul]

theorem allocatedFixedPathForecastDensity_cap_lipschitz
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let K := Real.toNNReal (anisotropicSpatialDensityLip s κ)
    let A := allocatedFixedPathLiftRowCap P ha hδ
    let Cs := C ^ Fintype.card X
    let Ks := Fintype.card X * K * C ^ Fintype.card X
    let Cl := ∏ j, A j
    let Kl := (∏ j, (A j + 1)) * ∑ j, A j * (2 * A j)
    (∀ y, density y ∈ Set.Icc (0 : ℝ) (Cs * Cl)) ∧
      LipschitzWith (Cl * Ks + Cs * Kl) density := by
  intro C K A Cs Ks Cl Kl
  have hf := canonicalZeroSpatialJointDensity_bounds (X := X) s root D hp hW hL
    hκ hroot hminor
  have hg := allocatedFixedPathLiftDensity_cap_lipschitz B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hgcap : ∀ y, g y ∈ Set.Icc (0 : ℝ) Cl := by
    simpa only [Cl, A, NNReal.coe_prod] using hg.1
  exact ⟨binaryDensity_cap f g Cs Cl hf.1 hgcap,
    binaryDensity_lipschitz f g Cs Cl Ks Kl hf.1 hgcap hf.2 hg.2⟩

theorem allocatedFixedPathForecastDensity_image_law
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (sigmaAxisMeasure (fun _ : X => Measure.map
      (canonicalSpatialKernelMap s root D (W := W) (L := L))
      (realDensityMeasure volume (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ Empty))))).prod
        ((unitBoxMeasure Input).map (allocatedFixedPathLiftMap B P R σ lower width r)) =
      realDensityMeasure volume density := by
  have hf := canonicalZeroSpatialJointDensity_bounds (X := X) s root D hp hW hL
    hκ hroot hminor
  have hg := allocatedFixedPathLiftDensity_cap_lipschitz B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hglaw := allocatedFixedPathLiftDensity_law_probability B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  rw [canonicalZeroSpatialJointDensity_image_law s root D hp hW hL, hglaw.1]
  exact binaryDensity_measure volume volume f g hf.2.continuous.measurable
    hg.2.continuous.measurable (fun y => (hf.1 y).1)

omit hR ha hδ hprincipal hw hl hr in
private theorem fixedPathDensity_unit_factor {Y : Type*} [PseudoMetricSpace Y]
    (φ : Y → ℝ) (C K : ℝ≥0) (hf : ∀ y, φ y ∈ Set.Icc (0 : ℝ) C)
    (hK : LipschitzWith K φ) :
    let F := fun y => (φ y : ℂ) / ((C : ℝ) + 1 : ℝ)
    (∀ y, ‖F y‖ ≤ 1) ∧ LipschitzWith K F ∧
      (∀ y, (φ y : ℂ) = (((C : ℝ) + 1 : ℝ) : ℂ) * F y) := by
  intro F
  have hpos : (0 : ℝ) < C + 1 := by positivity
  have hden : ‖(((C : ℝ) + 1 : ℝ) : ℂ)‖ = (C : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    change ‖(φ y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)‖ ≤ 1
    rw [norm_div, hden, Complex.norm_real, Real.norm_of_nonneg (hf y).1]
    exact (div_le_one hpos).mpr ((hf y).2.trans (by linarith))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((φ x : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ))
      ((φ y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ)) ≤ (K : ℝ) * dist x y
    rw [dist_eq_norm, ← sub_div, norm_div, ← Complex.ofReal_sub, Complex.norm_real, hden]
    have hd := hK.dist_le_mul x y
    rw [dist_eq_norm] at hd
    exact (div_le_self (norm_nonneg _) (by linarith [C.coe_nonneg] : (1 : ℝ) ≤ C + 1)).trans hd
  · intro y
    change (φ y : ℂ) = (((C : ℝ) + 1 : ℝ) : ℂ) *
      ((φ y : ℂ) / (((C : ℝ) + 1 : ℝ) : ℂ))
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

theorem allocatedFixedPathForecastDensity_normalized_bounds
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let K := Real.toNNReal (anisotropicSpatialDensityLip s κ)
    let A := allocatedFixedPathLiftRowCap P ha hδ
    let Cs := C ^ Fintype.card X
    let Ks := Fintype.card X * K * C ^ Fintype.card X
    let Cl := ∏ j, A j
    let Kl := (∏ j, (A j + 1)) * ∑ j, A j * (2 * A j)
    let H : ℝ := Cs * Cl + 1
    let F := fun y => (density y : ℂ) / (H : ℂ)
    (∀ y, ‖F y‖ ≤ 1) ∧ LipschitzWith (Cl * Ks + Cs * Kl) F ∧
      (∀ y, (density y : ℂ) = (H : ℂ) * F y) := by
  intro C K A Cs Ks Cl Kl H F
  have hb := allocatedFixedPathForecastDensity_cap_lipschitz (X := X)
    B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
    hκ hroot hminor
  exact fixedPathDensity_unit_factor density (Cs * Cl) (Cl * Ks + Cs * Kl) hb.1 hb.2

end Erdos3.VectorPolynomial

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

theorem forecastInactive_actual_smooth_factor_bounds
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    {Inactive Cell Site : Type*} [Fintype Inactive]
    (e : Cell → Inactive → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : Inactive → ℝ} {Lsite : ℝ≥0}
    (he : ∀ cell a, (e cell a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (t : Σ cell, ∀ a, (e cell a).Term) (site : Site)
    (res : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (χ : ℂ) (hχ : ‖χ‖ ≤ 1) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let K := Real.toNNReal (anisotropicSpatialDensityLip s κ)
    let Acap := allocatedFixedPathLiftRowCap P ha hδ
    let Cs := C ^ Fintype.card X
    let Ks := Fintype.card X * K * C ^ Fintype.card X
    let Cl := ∏ j, Acap j
    let Kl := (∏ j, (Acap j + 1)) * ∑ j, Acap j * (2 * Acap j)
    let H : ℝ := Cs * Cl + 1
    let F := fun y : ContinuousCoord × (Inactive → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    let factor := fun y : ContinuousCoord × (Inactive → ℝ) =>
      (χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2
    (∀ y, ‖factor y‖ ≤ 1) ∧
      LipschitzWith (Cl * Ks + Cs * Kl + Fintype.card Inactive * Lsite) factor ∧
      (∀ y, (∃ a, Hsite a ≤ |y.2 a|) → factor y = 0) ∧
      (∀ y, (χ * (density y.1 : ℂ)) * siteFamilyFactor (e t.1) t.2 site res y.2 =
        (H : ℂ) * factor y) := by
  intro C K Acap Cs Ks Cl Kl H F factor
  have hb := allocatedFixedPathForecastDensity_normalized_bounds (X := X)
    B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
    hκ hroot hminor
  have hF : ∀ y : ContinuousCoord × (Inactive → ℝ), ‖F y‖ ≤ 1 := fun y => hb.1 y.1
  have hFL : LipschitzWith (Cl * Ks + Cs * Kl) F := by
    simpa only [Function.comp_def, mul_one] using hb.2.1.comp
      (LipschitzWith.prod_fst (α := ContinuousCoord) (β := Inactive → ℝ))
  have hfactor := forecastSiteMixture_factor_comp_bounds e he t site res
    F hF hFL Prod.snd
    (LipschitzWith.prod_snd (α := ContinuousCoord) (β := Inactive → ℝ)) χ hχ
  refine ⟨hfactor.1, ?_, ?_, ?_⟩
  · simpa only [mul_one] using hfactor.2
  · intro y hy
    exact forecastSiteMixture_factor_comp_support e he t site res F Prod.snd χ y hy
  · intro y
    have hnorm : (density y.1 : ℂ) = (H : ℂ) * F y := hb.2.2 y.1
    change (χ * (density y.1 : ℂ)) * siteFamilyFactor (e t.1) t.2 site res y.2 =
      (H : ℂ) * ((χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2)
    rw [hnorm]
    ring

end Erdos3.VectorPolynomial

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

local notation "f" => canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL
local notation "g" => allocatedFixedPathLiftDensity B P R σ hB lower width r
local notation "density" => allocatedFixedPathForecastDensity (X := X) B P R σ s root D hp hW hL
  hB lower width r

include hR ha hδ hprincipal hw hl hr

theorem allocatedFixedPathForecastDensity_zero_off_ball
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (z : (Spatial → ℝ) × (Output → ℝ)) (hz : 3 < ‖z‖) : density z = 0 := by
  have hor : 3 < ‖z.1‖ ∨ 3 < ‖z.2‖ := by
    simpa only [Prod.norm_def, lt_max_iff] using hz
  rcases hor with hsp | hlift
  · change f z.1 * g z.2 = 0
    rw [canonicalZeroSpatialJointDensity_zero_outside s root D hp hW hL hroot z.1 hsp,
      zero_mul]
  · change f z.1 * g z.2 = 0
    rw [allocatedFixedPathLiftDensity_zero_off_ball B P R σ hR hB lower width hwidth
      ha hδ hprincipal hw hl r hr z.2 (by linarith), mul_zero]

theorem allocatedFixedPathForecastDensity_compact
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1) :
    HasCompactSupport density := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : (Spatial → ℝ) × (Output → ℝ)) 3)
  intro z hz
  exact allocatedFixedPathForecastDensity_zero_off_ball B P R σ s root D hp hW hL
    hR hB lower width ha hδ hprincipal hw hl r hr hroot hwidth z
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

private theorem forecast_singleton_site_eval
    {A : Type*} [Fintype A] (e : A → ScalarSiteExpansion (Finset Empty))
    (z : A → ℤ) (x : A → ℝ) :
    siteFamilyEval e (fun _ => z) (fun _ => x) =
      ∑ k, siteFamilyCoefficient e k * siteFamilyFactor e k ∅
        (fun a => (z a : ZMod ((e a).period (k a)))) x := by
  simp only [siteFamilyEval, Fintype.prod_unique]
  rfl

theorem forecastRetained_normalized_expansion
    {Q A : Type*} [Fintype Q] [Fintype A]
    {Cell : Q → Type*} [∀ q, Fintype (Cell q)]
    (e : ∀ q, Cell q → A → ScalarSiteExpansion (Finset Empty))
    (c : ∀ q, Cell q → ℂ) (phase : Q → ℂ)
    (z : A → ℤ) (x : A → ℝ) (G H F : ℂ) (hG : G = H * F) :
    G * (∑ q, (∑ r, c q r * siteFamilyEval (e q r) (fun _ => z) (fun _ => x)) * phase q) =
      ∑ t : Σ q, Σ r : Cell q, ∀ a, (e q r a).Term,
        (H * forecastSiteMixtureCoefficient (e t.1) (c t.1) t.2) *
          ((phase t.1 * F) * siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) x) := by
  simp_rw [forecast_singleton_site_eval]
  rw [Fintype.sum_sigma]
  simp only [Finset.mul_sum, Finset.sum_mul, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [forecastSiteMixtureCoefficient]
  rw [hG]
  ring

theorem forecastRetained_normalized_coefficient_mass
    {Q A : Type*} [Fintype Q] [Fintype A]
    {Cell : Q → Type*} [∀ q, Fintype (Cell q)]
    (e : ∀ q, Cell q → A → ScalarSiteExpansion (Finset Empty))
    (c : ∀ q, Cell q → ℂ) {H M : ℝ} (hH : 0 ≤ H)
    (hmass : (∑ q, ∑ t : Σ r : Cell q, ∀ a, (e q r a).Term,
      ‖forecastSiteMixtureCoefficient (e q) (c q) t‖) ≤ M) :
    (∑ t : Σ q, Σ r : Cell q, ∀ a, (e q r a).Term,
      ‖(H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (c t.1) t.2‖) ≤ H * M := by
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hH, Fintype.sum_sigma]
  simp only [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (by simpa only [Fintype.sum_sigma] using hmass) hH

end Erdos3

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

theorem forecastRetained_actual_smooth_expansion
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    {Q Inactive : Type*} [Fintype Q] [Fintype Inactive]
    {Cell : Q → Type*} [∀ q, Fintype (Cell q)]
    (e : ∀ q, Cell q → Inactive → ScalarSiteExpansion (Finset Empty))
    {Tsite Dsite Csite Hsite : Inactive → ℝ} {Lsite : ℝ≥0}
    (he : ∀ q cell i, (e q cell i).Bounds (Tsite i) (Dsite i) (Csite i) Lsite (Hsite i))
    (c : ∀ q, Cell q → ℂ) (phase : Q → ℂ) (hphase : ∀ q, ‖phase q‖ ≤ 1)
    {M : ℝ} (hmass : (∑ q, ∑ t : Σ cell : Cell q, ∀ i, (e q cell i).Term,
      ‖forecastSiteMixtureCoefficient (e q) (c q) t‖) ≤ M) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let K := Real.toNNReal (anisotropicSpatialDensityLip s κ)
    let Acap := allocatedFixedPathLiftRowCap P ha hδ
    let Cs := C ^ Fintype.card X
    let Ks := Fintype.card X * K * C ^ Fintype.card X
    let Cl := ∏ j, Acap j
    let Kl := (∏ j, (Acap j + 1)) * ∑ j, Acap j * (2 * Acap j)
    let H : ℝ := Cs * Cl + 1
    let F := fun y : ContinuousCoord × (Inactive → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    let Term := Σ q, Σ cell : Cell q, ∀ i, (e q cell i).Term
    let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (c t.1) t.2
    let factor := fun (t : Term) (z : Inactive → ℤ) (y : ContinuousCoord × (Inactive → ℝ)) =>
      (phase t.1 * F y) * siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
        (fun i => (z i : ZMod ((e t.1 t.2.1 i).period (t.2.2 i)))) y.2
    (∑ t : Term, ‖coeff t‖) ≤ H * M ∧
      (∀ t z y, ‖factor t z y‖ ≤ 1) ∧
      (∀ t z, LipschitzWith (Cl * Ks + Cs * Kl + Fintype.card Inactive * Lsite) (factor t z)) ∧
      ∀ (z : Inactive → ℤ) (y : ContinuousCoord × (Inactive → ℝ)),
        (density y.1 : ℂ) *
          (∑ q, (∑ cell, c q cell * siteFamilyEval (e q cell)
            (fun _ => z) (fun _ => y.2)) * phase q) =
          ∑ t : Term, coeff t * factor t z y := by
  intro C K Acap Cs Ks Cl Kl H F Term coeff factor
  have hb := allocatedFixedPathForecastDensity_normalized_bounds (X := X)
    B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
    hκ hroot hminor
  have hterm (t : Term) (z : Inactive → ℤ) :=
    forecastInactive_actual_smooth_factor_bounds (X := X)
      B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
      hκ hroot hminor (e t.1) (he t.1) t.2 ∅
      (fun i => (z i : ZMod ((e t.1 t.2.1 i).period (t.2.2 i)))) (phase t.1) (hphase t.1)
  refine ⟨forecastRetained_normalized_coefficient_mass e c (by positivity) hmass,
    (fun t z => (hterm t z).1), (fun t z => (hterm t z).2.1), ?_⟩
  intro z y
  exact forecastRetained_normalized_expansion e c phase z y.2
    (density y.1 : ℂ) (H : ℂ) (F y) (hb.2.2 y.1)

theorem forecastRetained_actual_smooth_error
    {κ : ℝ} (hκ : 0 < κ) (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    (y : ContinuousCoord) {target model : ℂ} {ε : ℝ}
    (happrox : ‖target - model‖ ≤ ε) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let Acap := allocatedFixedPathLiftRowCap P ha hδ
    let H : ℝ := C ^ Fintype.card X * (∏ j, Acap j) + 1
    ‖(density y : ℂ) * target - (density y : ℂ) * model‖ ≤ H * ε := by
  intro C Acap H
  have hb := allocatedFixedPathForecastDensity_normalized_bounds (X := X)
    B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
    hκ hroot hminor
  have hH : 0 ≤ H := by positivity
  have hcap : ‖(density y : ℂ)‖ ≤ H := by
    calc
      _ = ‖(H : ℂ) * ((density y : ℂ) / (H : ℂ))‖ := congrArg norm (hb.2.2 y)
      _ ≤ H * 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hH]
        exact mul_le_mul_of_nonneg_left (hb.1 y) hH
      _ = H := mul_one H
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right hcap (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left happrox hH)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {ContinuousCoord : Type*} [PseudoMetricSpace ContinuousCoord]
variable (density : ContinuousCoord → ℝ) (H : ℝ) (hH : 1 ≤ H)
variable (hdensity : ∀ y, ‖density y‖ ≤ H)
variable (densityLip : ℝ≥0) (hLip : LipschitzWith densityLip density)

include hH hdensity hLip in

theorem forecastContinuous_site_factor_bounds
    {A Cell Site : Type*} [Fintype A]
    (e : Cell → A → ScalarSiteExpansion Site)
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ cell a, (e cell a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (t : Σ cell, ∀ a, (e cell a).Term) (site : Site)
    (res : ∀ a, ZMod ((e t.1 a).period (t.2 a)))
    (χ : ℂ) (hχ : ‖χ‖ ≤ 1) :
    let F := fun y : ContinuousCoord × (A → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    let factor := fun y : ContinuousCoord × (A → ℝ) =>
      (χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2
    (∀ y, ‖factor y‖ ≤ 1) ∧
      LipschitzWith (densityLip + Fintype.card A * Lsite) factor ∧
      (∀ y, (∃ a, Hsite a ≤ |y.2 a|) → factor y = 0) ∧
      (∀ y, (χ * (density y.1 : ℂ)) * siteFamilyFactor (e t.1) t.2 site res y.2 =
        (H : ℂ) * factor y) := by
  intro F factor
  have hb := forecastContinuous_normalized_bounds density H hH hdensity densityLip hLip
  have hF : ∀ y : ContinuousCoord × (A → ℝ), ‖F y‖ ≤ 1 := fun y => hb.1 y.1
  have hFL : LipschitzWith densityLip F := by
    simpa only [Function.comp_def, mul_one] using hb.2.1.comp
      (LipschitzWith.prod_fst (α := ContinuousCoord) (β := A → ℝ))
  have hf := forecastSiteMixture_factor_comp_bounds e he t site res F hF hFL Prod.snd
    (LipschitzWith.prod_snd (α := ContinuousCoord) (β := A → ℝ)) χ hχ
  refine ⟨hf.1, ?_, ?_, ?_⟩
  · simpa only [mul_one] using hf.2
  · intro y hy
    exact forecastSiteMixture_factor_comp_support e he t site res F Prod.snd χ y hy
  · intro y
    have hn : (density y.1 : ℂ) = (H : ℂ) * F y := hb.2.2 y.1
    change (χ * (density y.1 : ℂ)) * siteFamilyFactor (e t.1) t.2 site res y.2 =
      (H : ℂ) * ((χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2)
    rw [hn]
    ring

include hH hdensity hLip in

theorem forecastRetained_continuous_expansion
    {Q A : Type*} [Fintype Q] [Fintype A]
    {Cell : Q → Type*} [∀ q, Fintype (Cell q)]
    (e : ∀ q, Cell q → A → ScalarSiteExpansion (Finset Empty))
    {Tsite Dsite Csite Hsite : A → ℝ} {Lsite : ℝ≥0}
    (he : ∀ q cell a, (e q cell a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite (Hsite a))
    (c : ∀ q, Cell q → ℂ) (phase : Q → ℂ) (hphase : ∀ q, ‖phase q‖ ≤ 1)
    {M : ℝ} (hmass : (∑ q, ∑ t : Σ cell : Cell q, ∀ a, (e q cell a).Term,
      ‖forecastSiteMixtureCoefficient (e q) (c q) t‖) ≤ M) :
    let F := fun y : ContinuousCoord × (A → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    let Term := Σ q, Σ cell : Cell q, ∀ a, (e q cell a).Term
    let coeff := fun t : Term => (H : ℂ) * forecastSiteMixtureCoefficient (e t.1) (c t.1) t.2
    let factor := fun (t : Term) (z : A → ℤ) (y : ContinuousCoord × (A → ℝ)) =>
      (phase t.1 * F y) * siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
        (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
    (∑ t : Term, ‖coeff t‖) ≤ H * M ∧
      (∀ t z y, ‖factor t z y‖ ≤ 1) ∧
      (∀ t z, LipschitzWith (densityLip + Fintype.card A * Lsite) (factor t z)) ∧
      ∀ (z : A → ℤ) (y : ContinuousCoord × (A → ℝ)),
        (density y.1 : ℂ) *
          (∑ q, (∑ cell, c q cell * siteFamilyEval (e q cell)
            (fun _ => z) (fun _ => y.2)) * phase q) =
          ∑ t : Term, coeff t * factor t z y := by
  intro F Term coeff factor
  have hb := forecastContinuous_normalized_bounds density H hH hdensity densityLip hLip
  have hterm (t : Term) (z : A → ℤ) :=
    forecastContinuous_site_factor_bounds density H hH hdensity densityLip hLip
      (e t.1) (he t.1) t.2 ∅
      (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) (phase t.1) (hphase t.1)
  refine ⟨forecastRetained_normalized_coefficient_mass e c (zero_le_one.trans hH) hmass,
    (fun t z => (hterm t z).1), (fun t z => (hterm t z).2.1), ?_⟩
  intro z y
  exact forecastRetained_normalized_expansion e c phase z y.2
    (density y.1 : ℂ) (H : ℂ) (F y) (hb.2.2 y.1)

omit [PseudoMetricSpace ContinuousCoord] in
include hH hdensity in

theorem forecastRetained_continuous_error (y : ContinuousCoord)
    {target model : ℂ} {ε : ℝ} (happrox : ‖target - model‖ ≤ ε) :
    ‖(density y : ℂ) * target - (density y : ℂ) * model‖ ≤ H * ε :=
  forecastContinuous_scaled_error density H hH hdensity y happrox

end Erdos3

end

end OAI
