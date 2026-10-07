/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
import OAI.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z]
  [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)

noncomputable def activeAveragedIdealSiteFunction (δ : ℝ≥0) (x : Finset α → D → ℝ) : ℂ :=
  activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
    (booleanSiteJets sets (fun s d => x s d.val))

omit [Fintype Z] in
theorem activeAveragedIdealSiteFunction_bound (δ : ℝ≥0) (hδ : 0 < δ)
    (x : Finset α → D → ℝ) :
    ‖activeAveragedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets δ x‖ ≤
      (δ⁻¹ ^ Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ≥0) := by
  have hx := (activeAveragedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ).1
    (booleanSiteJets sets (fun s d => x s d.val))
  simpa only [activeAveragedIdealSiteFunction, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx.1] using hx.2

omit [Fintype Z] in
theorem activeAveragedIdealSiteFunction_lipschitz (δ : ℝ≥0) (hδ : 0 < δ) :
    LipschitzWith
      (affineProductProfileLip (Σ d : {d // ¬P d}, O d.val) δ * (2 : ℝ≥0)^Fintype.card α)
      (activeAveragedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets δ) := by
  have hrestrict : LipschitzWith 1
      (fun x : Finset α → D → ℝ => fun s (d : {d // ¬P d}) => x s d.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro s
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro d
    exact (dist_le_pi_dist (x s) (y s) d.val).trans (dist_le_pi_dist x y s)
  have hi := (activeAveragedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ).2.1
  change LipschitzWith _ (fun x : Finset α → D → ℝ =>
    (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
      (booleanSiteJets sets (fun s d => x s d.val)) : ℂ))
  simpa only [one_mul, mul_one, Function.comp_def] using
    Complex.isometry_ofReal.lipschitzWith.comp
      (hi.comp ((booleanSiteJets_lipschitz sets).comp hrestrict))

omit [Fintype Z] in
theorem exists_active_ideal_site_approximation (δ : ℝ≥0) (hδ : 0 < δ)
    {R ε p : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*Q+8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ)
        (f : (Finset α × D → Fin n) → Finset α → (D → ℝ) → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α)*Fintype.card D : ℕ)*(4*Q+8)+Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*Q+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Finset α → D → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖(activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
              (booleanSiteJets sets (fun s d => x s d.val)) : ℂ) -
            ∑ k, a k*∏ s, f k s (x s)‖ ≤ ε := by
  intro Q
  have hcard : Fintype.card (Σ d : {d // ¬P d}, O d.val) ≤ Fintype.card (Σ d, O d) := by
    apply Fintype.card_le_of_injective (fun a : (Σ d : {d // ¬P d}, O d.val) =>
      (⟨a.1.val, a.2⟩ : Σ d, O d))
    rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ heq
    cases heq
    rfl
  have hcardR : (Fintype.card (Σ d : {d // ¬P d}, O d.val) : ℝ) ≤
      Fintype.card (Σ d, O d) := by exact_mod_cast hcard
  have hQle : idealSiteLogBudget (Fintype.card (Σ d : {d // ¬P d}, O d.val))
      (Fintype.card α) p ≤ Q := by
    dsimp only [Q, idealSiteLogBudget, affineProfileLogBound]
    gcongr
  have hb := idealSiteLogBudget_bounds (Fintype.card (Σ d, O d)) (Fintype.card α) hp
  have hprof := idealSiteProfile_bounds (Σ d : {d // ¬P d}, O d.val)
    (Fintype.card α) δ hδ hp hδp
  exact exists_grouped_site_approximation
    (activeAveragedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets δ)
    (δ⁻¹ ^ Fintype.card (Σ d : {d // ¬P d}, O d.val))
    (affineProductProfileLip (Σ d : {d // ¬P d}, O d.val) δ * (2 : ℝ≥0)^Fintype.card α)
    (activeAveragedIdealSiteFunction_bound h P sets δ hδ)
    (activeAveragedIdealSiteFunction_lipschitz h P sets δ hδ)
    hR hε hb.1 (hRp.trans (Real.exp_le_exp.mpr hb.2.1))
    (hprof.1.trans (Real.exp_le_exp.mpr hQle))
    (hprof.2.trans (Real.exp_le_exp.mpr hQle))
    (hεp.trans (Real.exp_le_exp.mpr hb.2.1))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
  (R : D → ℝ) (hR : ∀ d, 0 < R d)

noncomputable def physicalActiveProfileIdeal (δ : ℝ≥0) : ((Σ d, O d) → ℝ) → ℝ :=
  diagonalDensityTransport (fun o => R o.1.val) (fun o => (hR o.1.val).ne')
    (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ)

theorem physicalActiveProfileIdeal_eq (δ : ℝ≥0) (v : (Σ d, O d) → ℝ) :
    physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v =
      (∏ o : Σ d, O d, R o.1.val)⁻¹ *
        activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
          (fun o => v o / R o.1.val) := by
  rw [physicalActiveProfileIdeal, diagonalDensityTransport_eq,
    abs_of_pos (Finset.prod_pos (fun o _ => hR o.1.val))]

theorem physicalActiveProfileIdeal_measurable (δ : ℝ≥0) :
    Measurable (physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ) :=
  linearDensityPullback_measurable _
    (activeAveragedProfileIdeal_measurable (G := G) (B := B) Z h P sets δ)

theorem physicalActiveProfileIdeal_probability (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ v, 0 ≤ physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v) ∧
    Integrable (physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ) ∧
    (∫ v, physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v) = 1 := by
  obtain ⟨hb, _, hi, hint⟩ := activeAveragedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ
  refine ⟨linearDensityPullback_nonneg _ (fun v => (hb v).1),
    linearDensityPullback_integrable _ hi, ?_⟩
  change (∫ v, linearDensityPullback _ _ v) = 1
  rw [linearDensityPullback_integral, hint]

theorem physicalActiveProfileIdeal_test_integral (δ : ℝ≥0) (f : ((Σ d, O d) → ℝ) → ℝ) :
    (∫ v, physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v * f v) =
      ∫ v, activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ v *
        f (fun o => R o.1.val * v o) :=
  diagonalDensityTransport_test_integral _ _ _ f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_buffered_active_ideal_site_approximation
    {D G Z α U : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    [PseudoMetricSpace U] {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
    (δ : ℝ≥0) (hδ : 0 < δ)
    {R ε p : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p)
    (y : Finset α → U → D → ℝ) (χ : Finset α → U → ℂ) {L C : ℝ≥0}
    (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ) (f : (Finset α × D → Fin n) → Finset α → U → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ k s u, ‖f k s u‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ * L + C) (f k s)) ∧
        ∀ u : Finset α → U,
          ‖(∏ s, χ s (u s)) * (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
              (booleanSiteJets sets (fun s d => y s (u s) d.val)) : ℂ) -
            ∑ k, a k * ∏ s, f k s (u s)‖ ≤ ε := by
  obtain ⟨n, hn, a, f, ha, hf, hLip, herr⟩ :=
    exists_active_ideal_site_approximation (G := G) (Z := Z) (B := B) h P sets δ hδ hR hε hp hRp hεp hδp
  dsimp only
  refine ⟨n, hn, a, bufferedSiteFactor y χ f, ha, ?_, ?_, ?_⟩
  · exact bufferedSiteFactor_bound y χ f hχ1 hf
  · exact bufferedSiteFactor_lipschitz y χ f hy hχ hLip hχ1 hf
  · intro u
    exact bufferedSiteExpansion_error y χ
      (activeAveragedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets δ)
      a f hε.le hχ1 hsupport herr u

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
  (R : D → ℝ) (hR : ∀ d, 0 < R d)

theorem physicalActiveProfileIdeal_bound (δ : ℝ≥0) (hδ : 0 < δ) (v : (Σ d, O d) → ℝ) :
    |physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v| ≤
      (∏ o : Σ d, O d, R o.1.val)⁻¹ * (δ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0) := by
  have hp := (activeAveragedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ).1
    (fun o => v o / R o.1.val)
  have hJ : 0 ≤ (∏ o : Σ d, O d, R o.1.val)⁻¹ :=
    inv_nonneg.mpr (Finset.prod_nonneg (fun o _ => (hR o.1.val).le))
  rw [physicalActiveProfileIdeal_eq, abs_mul, abs_of_nonneg hJ, abs_of_nonneg hp.1]
  exact mul_le_mul_of_nonneg_left hp.2 hJ

theorem physicalActiveProfileIdeal_lipschitz (δ : ℝ≥0) (hδ : 0 < δ)
    (M : ℝ≥0) (hInv : ∀ d, (R d)⁻¹ ≤ M) :
    LipschitzWith (‖(∏ o : Σ d, O d, R o.1.val)⁻¹‖₊ *
      (affineProductProfileLip (Σ d, O d) δ * M))
      (physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ) := by
  have hs : LipschitzWith M
      (fun v : (Σ d, O d) → ℝ => fun o => v o / R o.1.val) := by
    have hc := coordinateScale_lipschitz (fun o : Σ d, O d => (R o.1.val)⁻¹)
      (fun o => (abs_of_pos (inv_pos.mpr (hR o.1.val))).le.trans (hInv o.1.val))
    simpa only [div_eq_mul_inv, mul_comm] using hc
  have hi := ((activeAveragedProfileIdeal_spec (G := G) (B := B) Z h P sets δ hδ).2.1).comp hs
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [Real.dist_eq, physicalActiveProfileIdeal_eq, ← mul_sub, abs_mul]
  simpa only [Function.comp_def, Real.dist_eq, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, mul_assoc]
    using mul_le_mul_of_nonneg_left (hi.dist_le_mul v w)
      (abs_nonneg ((∏ o : Σ d, O d, R o.1.val)⁻¹))

theorem physicalActiveProfileIdeal_zero_outside [Fintype Z] {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (M : ℝ≥0) (hRM : ∀ d, R d ≤ M)
    (v : (Σ d, O d) → ℝ)
    (hv : (M : ℝ) * (partitionedIdealRadius α degree + 1) < ‖v‖) :
    physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ v = 0 := by
  let w : (Σ d, O d) → ℝ := fun o => v o / R o.1.val
  have hrec : (fun o => R o.1.val * w o) = v := by
    funext o
    exact mul_div_cancel₀ (v o) (hR o.1.val).ne'
  have hs := coordinateScale_lipschitz (fun o : Σ d, O d => R o.1.val)
    (fun o => (abs_of_pos (hR o.1.val)).le.trans (hRM o.1.val))
  have hnorm : ‖v‖ ≤ (M : ℝ) * ‖w‖ := by
    have hh := hs.dist_le_mul w 0
    simp only [Pi.zero_apply, mul_zero] at hh
    change dist (fun o => R o.1.val * w o) 0 ≤ (M : ℝ) * dist w 0 at hh
    simpa only [hrec, dist_zero_right] using hh
  have hw : partitionedIdealRadius α degree + 1 < ‖w‖ := by
    apply lt_of_not_ge
    intro hw
    exact (not_lt_of_ge (hnorm.trans (mul_le_mul_of_nonneg_left hw M.coe_nonneg))) hv
  rw [physicalActiveProfileIdeal_eq,
    activeAveragedProfileIdeal_zero_outside Z h P sets hdegree δ hδ hδ1 w hw, mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem booleanSiteJets_axis_mul {D α : Type*} [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α) (R : D → ℝ)
    (x : Finset α → D → ℝ) :
    booleanSiteJets sets (fun s d => R d * x s d) =
      fun o => R o.1 * booleanSiteJets sets x o := by
  funext o
  exact booleanCoefficient_const_mul (sets o.1 o.2) (R o.1) (fun s => x s o.1)

theorem physicalActiveProfileIdeal_normalized_sites
    {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)
    (R : D → ℝ) (hR : ∀ d, 0 < R d) (δ : ℝ≥0) (x : Finset α → D → ℝ) :
    (∏ o : (Σ d : {d // ¬P d}, O d.val), R o.1.val) *
      physicalActiveProfileIdeal (G := G) (B := B) Z h P sets R hR δ
        (booleanSiteJets sets (fun s d => R d.val * x s d.val)) =
      activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
        (booleanSiteJets sets (fun s d => x s d.val)) := by
  have hJ : 0 < ∏ o : (Σ d : {d // ¬P d}, O d.val), R o.1.val :=
    Finset.prod_pos (fun o _ => hR o.1.val)
  rw [booleanSiteJets_axis_mul, physicalActiveProfileIdeal_eq]
  have hdiv : (fun o : (Σ d : {d // ¬P d}, O d.val) =>
      R o.1.val * booleanSiteJets sets (fun s d => x s d.val) o / R o.1.val) =
      booleanSiteJets sets (fun s d => x s d.val) := by
    funext o
    exact mul_div_cancel_left₀ _ (hR o.1.val).ne'
  rw [hdiv, ← mul_assoc, mul_inv_cancel₀ hJ.ne', one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_masked_active_ideal_site_approximation
    {D G Z α U R₀ : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    [PseudoMetricSpace U] [Fintype R₀]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α) (δ : ℝ≥0) (hδ : 0 < δ)
    {R ε p q : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p)
    (y : Finset α → U → D → ℝ) (χ : Finset α → U → ℂ) {L C : ℝ≥0}
    (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R)
    (label : Finset α → U → R₀) (mask : (Finset α → R₀) → ℂ)
    (hresidue : (Fintype.card R₀ : ℝ) ≤ Real.exp q) (hmask : ∀ r, ‖mask r‖ ≤ Real.exp q) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ) (f : (Finset α × D → Fin n) → Finset α → U → ℂ),
        (∑ r : Finset α → R₀, ∑ k, ‖mask r * a k‖) ≤
          Real.exp (Fintype.card (Finset α) * q + q +
            ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q)) ∧
        (∀ k s u, ‖f k s u‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ * L + C) (f k s)) ∧
        (∀ r k s u, ‖maskedSiteFactor label r f k s u‖ ≤ 1) ∧
        ∀ u : Finset α → U,
          ‖mask (fun s => label s (u s)) * ((∏ s, χ s (u s)) *
              (activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ
                (booleanSiteJets sets (fun s d => y s (u s) d.val)) : ℂ)) -
            ∑ r : Finset α → R₀, ∑ k, (mask r * a k) * ∏ s, maskedSiteFactor label r f k s (u s)‖ ≤
              Real.exp q * ε := by
  obtain ⟨n, hn, a, f, ha, hf, hLip, herr⟩ :=
    exists_buffered_active_ideal_site_approximation (G := G) (Z := Z) (B := B) h P sets δ hδ
      hR hε hp hRp hεp hδp y χ hy hχ hχ1 hsupport
  dsimp only
  refine ⟨n, hn, a, f, ?_, hf, hLip, ?_, ?_⟩
  · exact maskedSiteExpansion_coefficient_le_exp mask a hresidue hmask ha
  · exact fun r k s u => maskedSiteFactor_bound label r f hf k s u
  · intro u
    exact maskedSiteExpansion_error label mask
      (fun u => (∏ s, χ s (u s)) *
        activeAveragedIdealSiteFunction (G := G) (Z := Z) (B := B) h P sets δ (fun s => y s (u s)))
      a f (Real.exp_nonneg q) hmask herr u

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem inverseProduct_norm_le_exp {Q : Type*} [Fintype Q]
    (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q) {p : ℝ}
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) :
    ‖(∏ q, R q)⁻¹‖ ≤ Real.exp ((Fintype.card Q : ℝ) * p) := by
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => hR q))),
    ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ _q : Q, Real.exp p :=
      Finset.prod_le_prod₀ (fun q _ => inv_nonneg.mpr (hR q)) (fun q _ => hRi q)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

theorem diagonalProfileLip_le_exp {Q : Type*} [Fintype Q]
    (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q) {D p e : ℝ} {δ : ℝ≥0}
    (hp : 0 ≤ p) (he : 0 ≤ e)
    (hcard : (Fintype.card Q : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D)
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e) :
    (‖(∏ q, R q)⁻¹‖₊ *
      (affineProductProfileLip Q δ * NNReal.mk (Real.exp p) (Real.exp_pos p).le) : ℝ≥0) ≤
      Real.exp (D * p + 2 * D + (D + 1) * e + p) := by
  have hJ : ‖(∏ q, R q)⁻¹‖ ≤ Real.exp (D * p) :=
    (inverseProduct_norm_le_exp R hR hRi).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hp))
  have hL : (affineProductProfileLip Q δ : ℝ) ≤ Real.exp (2 * D + (D + 1) * e) := by
    apply (affineProductProfileLip_le_exp Q hδ).trans
    apply Real.exp_le_exp.mpr
    unfold affineProfileLogBound
    nlinarith
  simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nnnorm]
  calc
    _ ≤ Real.exp (D * p) * (Real.exp (2 * D + (D + 1) * e) * Real.exp p) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem partitionedIdealRadius_add_one_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    partitionedIdealRadius α degree + 1 ≤
      Real.exp (((degree : ℝ) + 1) * (Fintype.card α : ℝ) + 2) := by
  let n : ℝ := Fintype.card α
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ Fintype.card α ≤ Real.exp n := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one, n]
  have hbase : n + 1 ≤ Real.exp n := Real.add_one_le_exp n
  have hmain : (2 : ℝ) ^ Fintype.card α * (n + 1) ^ degree ≤
      Real.exp (((degree : ℝ) + 1) * n) := by
    calc
      _ ≤ Real.exp n * (Real.exp n) ^ degree := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (((degree : ℝ) + 1) * n) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (((degree : ℝ) + 1) * n) := by
      unfold partitionedIdealRadius
      change 1 / 4 + 2 ^ Fintype.card α * (n + 1) ^ degree + 1 ≤ _
      linarith
    _ ≤ Real.exp 2 * Real.exp (((degree : ℝ) + 1) * n) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_masked_physical_active_ideal_site_approximation
    {D G Z α U R₀ : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
    [PseudoMetricSpace U] [Fintype R₀]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (sets : ∀ d : {d // ¬P d}, O d.val → Finset α) (δ : ℝ≥0) (hδ : 0 < δ)
    (scale : D → ℝ) (hscale : ∀ d, 0 < scale d)
    {R ε p q : ℝ} (hR : 0 < R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hRp : R ≤ Real.exp p) (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p)
    (y : Finset α → U → D → ℝ) (χ : Finset α → U → ℂ) {L C : ℝ≥0}
    (hy : ∀ s, LipschitzWith L (y s)) (hχ : ∀ s, LipschitzWith C (χ s))
    (hχ1 : ∀ s u, ‖χ s u‖ ≤ 1) (hsupport : ∀ s u, χ s u ≠ 0 → ∀ d, |y s u d| ≤ R)
    (label : Finset α → U → R₀) (mask : (Finset α → R₀) → ℂ)
    (hresidue : (Fintype.card R₀ : ℝ) ≤ Real.exp q) (hmask : ∀ r, ‖mask r‖ ≤ Real.exp q) :
    let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card ((Finset α → R₀) × (Finset α × D → Fin n)) : ℝ) ≤
        Real.exp (Fintype.card (Finset α) * q +
          (Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × D → Fin n) → ℂ) (f : (Finset α × D → Fin n) → Finset α → U → ℂ),
        (∑ r : Finset α → R₀, ∑ k, ‖mask r * a k‖) ≤
          Real.exp (Fintype.card (Finset α) * q + q +
            ((Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8) + Q)) ∧
        (∀ k s u, ‖f k s u‖ ≤ 1) ∧
        (∀ k s, LipschitzWith (⟨Real.exp (Fintype.card D + 6 * Q + 12), Real.exp_nonneg _⟩ * L + C) (f k s)) ∧
        (∀ r k s u, ‖maskedSiteFactor label r f k s u‖ ≤ 1) ∧
        ∀ u : Finset α → U,
          ‖mask (fun s => label s (u s)) * ((∏ s, χ s (u s)) *
              (((∏ o : (Σ d : {d // ¬P d}, O d.val), scale o.1.val : ℝ) : ℂ) *
                (physicalActiveProfileIdeal (G := G) (B := B) Z h P sets scale hscale δ
                  (booleanSiteJets sets (fun s d => scale d.val * y s (u s) d.val)) : ℂ))) -
            ∑ r : Finset α → R₀, ∑ k, (mask r * a k) * ∏ s, maskedSiteFactor label r f k s (u s)‖ ≤
              Real.exp q * ε ∧
          ‖mask (fun s => label s (u s)) * ((∏ s, χ s (u s)) *
              (physicalActiveProfileIdeal (G := G) (B := B) Z h P sets scale hscale δ
                (booleanSiteJets sets (fun s d => scale d.val * y s (u s) d.val)) : ℂ)) -
            (∑ r : Finset α → R₀, ∑ k, (mask r * a k) * ∏ s, maskedSiteFactor label r f k s (u s)) /
              ((∏ o : (Σ d : {d // ¬P d}, O d.val), scale o.1.val : ℝ) : ℂ)‖ ≤
            (Real.exp q * ε) / (∏ o : (Σ d : {d // ¬P d}, O d.val), scale o.1.val) := by
  obtain ⟨n, hn, a, f, ha, hf, hLip, hmf, herr⟩ :=
    exists_masked_active_ideal_site_approximation (G := G) (Z := Z) (B := B) h P sets δ hδ
      hR hε hp hRp hεp hδp y χ hy hχ hχ1 hsupport label mask hresidue hmask
  let Q := idealSiteLogBudget (Fintype.card (Σ d, O d)) (Fintype.card α) p
  have hcard : (Fintype.card ((Finset α → R₀) × (Finset α × D → Fin n)) : ℝ) ≤
      Real.exp (Fintype.card (Finset α) * q +
        (Fintype.card (Finset α) * Fintype.card D : ℕ) * (4 * Q + 8)) := by
    have hc : (Fintype.card ((Finset α → R₀) × (Finset α × D → Fin n)) : ℝ) =
        (Fintype.card R₀ : ℝ) ^ Fintype.card (Finset α) *
          (n : ℝ) ^ (Fintype.card (Finset α) * Fintype.card D) := by simp
    rw [hc]
    calc
      _ ≤ (Real.exp q) ^ Fintype.card (Finset α) *
          (Real.exp (4 * Q + 8)) ^ (Fintype.card (Finset α) * Fintype.card D) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  dsimp only
  refine ⟨n, hn, hcard, a, f, ha, hf, hLip, hmf, ?_⟩
  intro u
  have hnrm := physicalActiveProfileIdeal_normalized_sites (G := G) (Z := Z) (B := B)
    h P sets scale hscale δ (fun s => y s (u s))
  have hc := congrArg Complex.ofReal hnrm
  simp only [Complex.ofReal_mul] at hc
  have htarget :
      ‖mask (fun s => label s (u s)) * ((∏ s, χ s (u s)) *
          (((∏ o : (Σ d : {d // ¬P d}, O d.val), scale o.1.val : ℝ) : ℂ) *
            (physicalActiveProfileIdeal (G := G) (B := B) Z h P sets scale hscale δ
              (booleanSiteJets sets (fun s d => scale d.val * y s (u s) d.val)) : ℂ))) -
        ∑ r : Finset α → R₀, ∑ k, (mask r * a k) * ∏ s, maskedSiteFactor label r f k s (u s)‖ ≤
        Real.exp q * ε := by
    rw [hc]
    exact herr u
  refine ⟨htarget, ?_⟩
  let J : ℝ := ∏ o : (Σ d : {d // ¬P d}, O d.val), scale o.1.val
  let z : ℂ := mask (fun s => label s (u s)) * ((∏ s, χ s (u s)) *
    (physicalActiveProfileIdeal (G := G) (B := B) Z h P sets scale hscale δ
      (booleanSiteJets sets (fun s d => scale d.val * y s (u s) d.val)) : ℂ))
  let F : ℂ := ∑ r : Finset α → R₀, ∑ k, (mask r * a k) * ∏ s, maskedSiteFactor label r f k s (u s)
  have hJ : 0 < J := Finset.prod_pos (fun o _ => hscale o.1.val)
  have hJC : (J : ℂ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hmult : ‖(J : ℂ) * z - F‖ ≤ Real.exp q * ε := by
    convert htarget using 1
    congr 1
    dsimp only [J, z, F]
    ring
  change ‖z - F / (J : ℂ)‖ ≤ (Real.exp q * ε) / J
  calc
    _ = ‖((J : ℂ) * z - F) / (J : ℂ)‖ := by
      congr 1
      field_simp [hJC]
    _ = ‖(J : ℂ) * z - F‖ / J := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hJ]
    _ ≤ _ := div_le_div_of_nonneg_right hmult hJ.le

end Erdos3

end

end OAI
