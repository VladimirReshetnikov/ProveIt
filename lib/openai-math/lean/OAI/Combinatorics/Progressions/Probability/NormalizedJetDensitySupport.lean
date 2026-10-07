import OAI.Combinatorics.Progressions.Estimates.NormalizedJetColumns
import OAI.Combinatorics.Progressions.Estimates.SplitPivotParameter
import OAI.Combinatorics.Progressions.Polynomial.PolynomialColumnSupport

namespace OAI


namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeProfile_integrable {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    Integrable (splitFreeProfile f g) := by
  apply (splitFreeProfile_continuous hf hg).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J ⊕ N → ℝ) × (I → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hp (splitFreeProfile_zero_outside hfs hgs p h)

theorem splitFreeProfile_integral {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    (∫ p, splitFreeProfile f g p) = (∫ p, f p) * ∫ n, g n := by
  have hfi : Integrable f := by
    apply hf.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : (J → ℝ) × (I → ℝ)) R)
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! h
    exact hp (hfs p h)
  have hi := splitFreeProfile_integrable hf hg hfs hgs
  rw [Measure.volume_eq_prod, integral_prod _ hi]
  have heq (y : J ⊕ N → ℝ) :
      (∫ x : I → ℝ, splitFreeProfile f g (y, x)) =
        splitInputProfile (fun p : (J → ℝ) × (N → ℝ) => (∫ x, f (p.1, x)) * g p.2) y := by
    unfold splitFreeProfile splitInputProfile
    exact integral_mul_const (g (fun n => y (.inr n)))
      (fun x => f ((fun j => y (.inl j)), x))
  simp_rw [heq]
  rw [splitInputProfile_integral, Measure.volume_eq_prod,
    integral_prod_mul (fun y : J → ℝ => ∫ x, f (y, x)) g, ← integral_prod f hfi]
  rfl

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_norm_le {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {H Q : ℝ} (hH : 0 ≤ H)
    (hf : ∀ p, ‖f p‖ ≤ H) (hg : ∀ n, ‖g n‖ ≤ Q) (p) :
    ‖splitFreeProfile f g p‖ ≤ H * Q := by
  rw [splitFreeProfile, norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hH

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def normalizedJetDensity {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (x : P → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity A
    (splitFreeColumns F (polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x))
    (splitFreeProfile f g)

theorem normalizedJetDensity_law {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ u, R < ‖u‖ → f u = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ n, 0 ≤ g n) (x : P → ℝ) :
    (realDensityMeasure volume (splitFreeProfile f g)).map
      (fun u => A u.2 + F (fun j => u.1 (.inl j)) +
        fun o => booleanCoefficient (fun t => ∑ n, u.1 (.inr n) * ∏ k ∈ (e n).support,
          (normalizedCubeTuple input z x t k)^e n k) (rows o)) =
      realDensityMeasure volume (normalizedJetDensity A F e input z rows f g x) := by
  have he : (fun u : (J ⊕ N → ℝ) × (I → ℝ) => A u.2 +
      splitFreeColumns F (polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x) u.1) =
      (fun u : (J ⊕ N → ℝ) × (I → ℝ) => A u.2 + F (fun j => u.1 (.inl j)) +
        fun o => booleanCoefficient (fun t => ∑ n, u.1 (.inr n) * ∏ k ∈ (e n).support,
          (normalizedCubeTuple input z x t k)^e n k) (rows o)) := by
    funext u
    rw [splitFreeColumns_apply, ← add_assoc]
    congr 1
    funext o
    exact normalizedJetColumns_apply_coefficients e input z rows x (fun n => u.1 (.inr n)) o
  rw [← he]
  exact pivotOutputDensity_law A _ (splitFreeProfile_integrable hf hg hfs hgs)
    (splitFreeProfile_nonneg hf0 hg0)

theorem normalizedJetDensity_bounds {Z P K α I J N : Type*}
    [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (R H Kf S : ℝ≥0) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith Kf f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ u, ‖f u‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1) (v : I → ℝ) :
    (∀ x, ‖normalizedJetDensity A F e input z rows f g x v‖ ≤ pivotKernelCap J A R H) ∧
    LipschitzOnWith (pivotKernelLip J A R Kf *
      (Fintype.card N * polynomialBoxLip (Fintype.card P) degree (normalizedJetMass α degree)) * S)
      (fun x => normalizedJetDensity A F e input z rows f g x v) (Metric.closedBall 0 1) := by
  constructor
  · intro x
    exact splitPivotDensity_norm_le_cap A F _ R H S hf.continuous hg hfs hgs hfb hg0 hgmass v
  · exact splitPivotDensity_parameter_lipschitzOn A F _ (Metric.closedBall 0 1) _ R Kf S
      (normalizedJetColumns_lipschitzOn_box e input z hz rows hd) hf hg hfs hgs hg0 hgmass v

end Erdos3


namespace Erdos3

open scoped NNReal

noncomputable def normalizedJetOutputRadius {I J : Type*} [Fintype I] [Fintype J]
    (α N : Type*) [Fintype α] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (degree : ℕ) (R S : ℝ≥0) : ℝ≥0 :=
  (‖A.toContinuousLinearMap‖₊+‖F‖₊)*R + (Fintype.card N * normalizedJetMass α degree)*S

theorem normalizedJetDensity_zero_outside {Z P K α I J N : Type*}
    [Fintype P] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (R S : ℝ≥0) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (x : P → ℝ) (hx : ‖x‖ ≤ 1) (v : I → ℝ)
    (hv : (normalizedJetOutputRadius α N A F degree R S : ℝ) < ‖v‖) :
    normalizedJetDensity A F e input z rows f g x v = 0 := by
  have hmass (o) (n) : realPolynomialMass (normalizedJetColumn (e n) input z (rows o)) ≤
      (normalizedJetMass α degree : ℝ) := normalizedJetColumn_mass_le (e n) input z hz (rows o) (hd n)
  have hcols := polynomialColumns_norm_le_on_box _ (normalizedJetMass α degree).coe_nonneg hmass x hx
  exact splitPivotDensity_zero_outside A F _ hf hg hfs hgs hcols v hv

end Erdos3

end OAI
