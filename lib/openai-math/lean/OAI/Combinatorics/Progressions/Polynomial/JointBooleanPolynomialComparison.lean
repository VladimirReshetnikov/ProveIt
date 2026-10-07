import OAI.Combinatorics.Progressions.Estimates.JointBooleanStability

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α Z : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [Fintype Z] [DecidableEq Z]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBoolean_polynomial_comparison {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (A T : ℝ≥0)
    (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    (p : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    {degree : ℕ} (hpdeg : ∀ o i, (p o).degreeOf i ≤ degree)
    {Cp : ℝ} (hCp : 0 ≤ Cp) (hpcoeff : ∀ o m, |(p o).coeff m| ≤ Cp)
    (z : Z → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (hpzero : parameterPolynomialMap p 0 z = jointBooleanSampler h c sets)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hsmall : (K : ℝ) * (t * polynomialC2BoxBudget
      (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp) ≤ 1 / 2)
    (hsecond : t * polynomialC2BoxBudget
      (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp ≤ 1)
    {η : ℝ} (hmass : 1 - η ≤ ∫ x, jointBooleanGoodWeight c sets block v sel ψ r κ x)
    (φ : ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp
    let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
    let Q := 1 + 2 * (K : ℝ) * S +
      (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * ((H : ℝ) + 1))
    |(∫ x, φ (jointBooleanSampler h c sets x) ∂jointBooleanSource h) -
      ∫ x, φ (parameterPolynomialMap p t z x) ∂jointBooleanSource h| ≤
      2 * η + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * (t * (1 + M))) := by
  let U := jointBooleanSampler h c sets
  let V := parameterPolynomialMap p t z
  let w := jointBooleanGoodWeight c sets block v sel ψ r κ
  let J := jointBooleanInjection block v sel
  let M := polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp
  have hM : 0 ≤ M := polynomialC2BoxBudget_nonneg _ _ hCp
  have hU : ContDiff ℝ 2 U := (jointBooleanSampler_contDiff h c sets).of_le (by norm_num)
  have hV : ContDiff ℝ 2 V := (parameterPolynomialMap_contDiff p t z).of_le (by norm_num)
  have hw := jointBooleanGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  have herr (x) (hx : x ∈ tsupport w) :
      ‖V x - U x‖ ≤ t * M ∧ ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ t * M ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ t * M := by
    have he := parameterPolynomialMap_uniform_c2_error p hpdeg hCp hpcoeff
      (show |t| ≤ 1 by rwa [abs_of_pos ht]) z hz x (hw.2.2.2.2 x hx).1
    rw [hpzero, abs_of_pos ht] at he
    exact he
  have hsmall' (x) (hx : x ∈ tsupport w) : (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (herr x hx).2.1 K.coe_nonneg).trans hsmall
  have hHV (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ (H + 1 : ℝ≥0) := by
    have hHU := jointBoolean_selected_derivative_bound c sets block v sel hcard x C (fun _ => 1)
      hC (fun _ => le_rfl) hc (hw.2.2.2.2 x hx).1 H.coe_nonneg hH
    have he := selectedDerivative_bound_of_second_error U V hU hV J
      (jointBooleanInjection_norm_le block hblock v sel) x hHU (herr x hx).2.2
    exact he.trans (add_le_add le_rfl hsecond)
  have hclose (x) (hx : w x ≠ 0) : dist (U x) (V x) ≤ t * (1 + M) := by
    rw [dist_comm, dist_eq_norm]
    exact (herr x (subset_closure hx)).1.trans (by nlinarith)
  have heps : 0 < t * (1 + M) := mul_pos ht (by linarith)
  have hcap (d : D) : productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ (H + 1 : ℝ≥0) :=
    (hH d).trans (by simp)
  have he := jointBoolean_good_weight_comparison c sets block hblock v sel hcard C hC hc
    ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K (H + 1) hK hcap
    V hV hsmall' hHV heps hmass hclose φ hφ hbound
  simpa only [NNReal.coe_add, NNReal.coe_one] using he

end Erdos3

end

end OAI
