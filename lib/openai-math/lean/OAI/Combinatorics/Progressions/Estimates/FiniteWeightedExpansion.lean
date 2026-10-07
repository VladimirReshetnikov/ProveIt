/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
import OAI.Combinatorics.Progressions.Sampling.JointGridAccuracy

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def jointRetainedExpansion {D : Type*} [Fintype D] [DecidableEq D]
    {A Z : D → Type*} (S : ∀ d, Finset (A d)) (c : ∀ d, A d → ℂ)
    (ψ : ∀ d, A d → Z d → ℂ) (z : ∀ d, Z d) : ℂ :=
  ∑ a : ∀ d, S d, (∏ d, c d (a d)) * ∏ d, ψ d (a d) (z d)

theorem jointRetainedExpansion_eq_product {D : Type*} [Fintype D] [DecidableEq D]
    {A Z : D → Type*} (S : ∀ d, Finset (A d)) (c : ∀ d, A d → ℂ)
    (ψ : ∀ d, A d → Z d → ℂ) (z : ∀ d, Z d) :
    jointRetainedExpansion S c ψ z = ∏ d, ∑ a ∈ S d, c d a * ψ d a (z d) := by
  rw [jointRetainedExpansion, ← finiteTensorExpansion
    (fun d (a : S d) => c d a) (fun d (a : S d) z => ψ d a z) z]
  apply Finset.prod_congr rfl
  intro d _
  exact Finset.sum_coe_sort (S d) (fun a => c d a * ψ d a (z d))

theorem jointRetainedExpansion_count {D : Type*} [Fintype D] [DecidableEq D]
    {A : D → Type*} (S : ∀ d, Finset (A d)) :
    Fintype.card (∀ d, S d) = ∏ d, (S d).card := by
  simp only [Fintype.card_pi, Fintype.card_coe]

theorem jointRetainedExpansion_coefficient_mass {D : Type*} [Fintype D] [DecidableEq D]
    {A : D → Type*} (S : ∀ d, Finset (A d)) (c : ∀ d, A d → ℂ) :
    (∑ a : ∀ d, S d, ‖∏ d, c d (a d)‖) = ∏ d, ∑ a ∈ S d, ‖c d a‖ := by
  rw [finiteTensorCoefficientMass (fun d (a : S d) => c d a)]
  apply Finset.prod_congr rfl
  intro d _
  exact Finset.sum_coe_sort (S d) (fun a => ‖c d a‖)

theorem jointRetainedExpansion_mass_bound {D : Type*} [Fintype D] [DecidableEq D]
    {A : D → Type*} (S : ∀ d, Finset (A d)) (c : ∀ d, A d → ℂ) {C : ℝ}
    (hC : ∀ d, (∑ a ∈ S d, ‖c d a‖) ≤ C) :
    (∑ a : ∀ d, S d, ‖∏ d, c d (a d)‖) ≤ C ^ Fintype.card D := by
  rw [jointRetainedExpansion_coefficient_mass]
  calc
    _ ≤ ∏ _d : D, C := Finset.prod_le_prod₀ (fun d _ => Finset.sum_nonneg (fun a _ => norm_nonneg _))
      (fun d _ => hC d)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

theorem retainedExpansion_norm_bound {A Z : Type*} (S : Finset A) (c : A → ℂ)
    (ψ : A → Z → ℂ) (z : Z) {C : ℝ} (hc : (∑ a ∈ S, ‖c a‖) ≤ C)
    (hψ : ∀ a ∈ S, ‖ψ a z‖ ≤ 1) : ‖∑ a ∈ S, c a * ψ a z‖ ≤ C := by
  apply (norm_sum_le _ _).trans
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hψ a ha)

theorem joint_retained_integer_approximation {D : Type*} [Fintype D] [DecidableEq D]
    {X J A : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (H : D → ℝ) (K : D → ℕ) (hK : ∀ d, 0 < K d) (hH : ∀ d, 0 ≤ H d)
    (center z : ∀ d, J d → ℤ)
    (hY : ∀ d x, (p d).weight x ≠ 0 → ∀ j, |(Y d x j : ℝ) - center d j| ≤ H d * K d)
    (hz : ∀ d, centeredFundamentalBox (commonSupportRadius H) (K d) (center d) (z d))
    (S : ∀ d, Finset (A d)) (c : ∀ d, A d → ℂ) (ψ : ∀ d, A d → (J d → ℤ) → ℂ)
    {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (hcap : ∀ d, ‖(integerGridDensity (p d) (Y d) (K d)
      ((2 * commonSupportRadius H + 1) * K d) (z d) : ℂ)‖ ≤ C)
    (hc : ∀ d, (∑ a ∈ S d, ‖c d a‖) ≤ C) (hψ : ∀ d a, a ∈ S d → ‖ψ d a (z d)‖ ≤ 1)
    (herror : ∀ d, ‖(integerGridDensity (p d) (Y d) (K d)
      ((2 * commonSupportRadius H + 1) * K d) (z d) : ℂ) -
        ∑ a ∈ S d, c d a * ψ d a (z d)‖ ≤ jointGridAxisTolerance (Fintype.card D) C ε) :
    ‖(((∏ d, (K d : ℝ) ^ Fintype.card (J d)) *
      finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z : ℝ) : ℂ) -
        jointRetainedExpansion S c ψ z‖ ≤ ε := by
  rw [jointRetainedExpansion_eq_product]
  exact joint_integer_density_approximation p Y H K hK hH center z hY hz
    (fun d => ∑ a ∈ S d, c d a * ψ d a (z d)) hC hε hcap
    (fun d => retainedExpansion_norm_bound (S d) (c d) (ψ d) (z d) (hc d) (hψ d)) herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_mixture_sub_le {R : Type*} [Fintype R]
    (w : R → ℝ) (a b : R → ℂ) (ε : R → ℝ) (hw : ∀ r, 0 ≤ w r)
    (he : ∀ r, ‖a r - b r‖ ≤ ε r) :
    ‖(∑ r, (w r : ℂ) * a r) - (∑ r, (w r : ℂ) * b r)‖ ≤ ∑ r, w r * ε r := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw r)]
  exact mul_le_mul_of_nonneg_left (he r) (hw r)

theorem norm_weighted_mixture_sub_le_uniform {R : Type*} [Fintype R]
    (w : R → ℝ) (a b : R → ℂ) {ε : ℝ} (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1) (hε : 0 ≤ ε) (he : ∀ r, ‖a r - b r‖ ≤ ε) :
    ‖(∑ r, (w r : ℂ) * a r) - (∑ r, (w r : ℂ) * b r)‖ ≤ ε := by
  apply (norm_weighted_mixture_sub_le w a b (fun _ => ε) hw he).trans
  rw [← Finset.sum_mul]
  exact mul_le_of_le_one_left hε hmass

noncomputable def weightedMixtureExpansion {R Z : Type*} [Fintype R]
    {A : R → Type*} [∀ r, Fintype (A r)]
    (w : R → ℝ) (c : ∀ r, A r → ℂ) (ψ : ∀ r, A r → Z → ℂ) (z : Z) : ℂ :=
  ∑ t : Σ r, A r, ((w t.1 : ℂ) * c t.1 t.2) * ψ t.1 t.2 z

theorem weightedMixtureExpansion_eq_sum {R Z : Type*} [Fintype R]
    {A : R → Type*} [∀ r, Fintype (A r)]
    (w : R → ℝ) (c : ∀ r, A r → ℂ) (ψ : ∀ r, A r → Z → ℂ) (z : Z) :
    weightedMixtureExpansion w c ψ z = ∑ r, (w r : ℂ) * ∑ a, c r a * ψ r a z := by
  simp only [weightedMixtureExpansion, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

theorem weightedMixtureExpansion_coefficient_mass {R : Type*} [Fintype R]
    {A : R → Type*} [∀ r, Fintype (A r)]
    (w : R → ℝ) (c : ∀ r, A r → ℂ) (hw : ∀ r, 0 ≤ w r) :
    (∑ t : Σ r, A r, ‖(w t.1 : ℂ) * c t.1 t.2‖) = ∑ r, w r * ∑ a, ‖c r a‖ := by
  simp only [Fintype.sum_sigma, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hw _), Finset.mul_sum]

theorem weightedMixtureExpansion_mass_le {R : Type*} [Fintype R]
    {A : R → Type*} [∀ r, Fintype (A r)]
    (w : R → ℝ) (c : ∀ r, A r → ℂ) (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ r, (∑ a, ‖c r a‖) ≤ C) :
    (∑ t : Σ r, A r, ‖(w t.1 : ℂ) * c t.1 t.2‖) ≤ C := by
  rw [weightedMixtureExpansion_coefficient_mass w c hw]
  calc
    _ ≤ ∑ r, w r * C := Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hc r) (hw r))
    _ = (∑ r, w r) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ C := mul_le_of_le_one_left hC hmass

theorem weightedMixtureExpansion_card_le {R : Type*} [Fintype R]
    (A : R → Type*) [∀ r, Fintype (A r)] (B : R → ℝ)
    (hB : ∀ r, (Fintype.card (A r) : ℝ) ≤ B r) :
    (Fintype.card (Σ r, A r) : ℝ) ≤ ∑ r, B r := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  exact Finset.sum_le_sum (fun r _ => hB r)

theorem weightedMixtureExpansion_approximation {R Z : Type*} [Fintype R]
    {A : R → Type*} [∀ r, Fintype (A r)]
    (w : R → ℝ) (c : ∀ r, A r → ℂ) (ψ : ∀ r, A r → Z → ℂ)
    (f : R → Z → ℂ) (z : Z) {ε : ℝ} (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1) (hε : 0 ≤ ε)
    (he : ∀ r, ‖f r z - ∑ a, c r a * ψ r a z‖ ≤ ε) :
    ‖(∑ r, (w r : ℂ) * f r z) - weightedMixtureExpansion w c ψ z‖ ≤ ε := by
  rw [weightedMixtureExpansion_eq_sum]
  exact norm_weighted_mixture_sub_le_uniform w (fun r => f r z)
    (fun r => ∑ a, c r a * ψ r a z) hw hmass hε he

end Erdos3

end

end OAI
