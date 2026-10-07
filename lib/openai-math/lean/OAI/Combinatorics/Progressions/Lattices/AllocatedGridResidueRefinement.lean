import OAI.Combinatorics.Progressions.Sampling.AllocatedBufferedGridIdeal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem residueSelectedSiteProduct {S R : Type*} [Fintype S] [Fintype R] [DecidableEq R]
    (label : S → R) (f : R → S → ℂ) :
    (∏ s, f (label s) s) =
      ∑ r : S → R, ∏ s, (if label s = r s then (1 : ℂ) else 0) * f (r s) s := by
  symm
  rw [Finset.sum_eq_single label]
  · simp
  · intro r _ hr
    have hne : ∃ s, label s ≠ r s := by
      by_contra h
      apply hr
      funext s
      exact (not_ne_iff.mp (not_exists.mp h s)).symm
    obtain ⟨s, hs⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp only [hs, ite_false, zero_mul])
  · simp

variable {A V : Type*} [Fintype A] (e : A → ScalarSiteExpansion V)
variable (k : ∀ a, (e a).Term) [∀ a, NeZero ((e a).period (k a))]

theorem gridResidueLabels_card :
    Fintype.card (∀ a, ZMod ((e a).period (k a))) = commonSitePeriod e k := by
  simp only [Fintype.card_pi, ZMod.card, commonSitePeriod]

theorem gridResidueLabels_card_le_exp
    {T C H K : A → ℝ} {L : ℝ≥0} (he : ∀ a, (e a).Bounds (T a) (C a) (H a) L (K a))
    {D E : ℝ} (hE : 0 ≤ E) (hA : (Fintype.card A : ℝ) ≤ D)
    (hperiod : ∀ a, C a ≤ Real.exp E) :
    (Fintype.card (∀ a, ZMod ((e a).period (k a))) : ℝ) ≤ Real.exp (D * E) := by
  rw [gridResidueLabels_card]
  apply (commonSitePeriod_le_pow e he hperiod k).trans
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA hE)

theorem gridSiteResidueLabels_card_le_exp [Fintype V]
    {T C H K : A → ℝ} {L : ℝ≥0} (he : ∀ a, (e a).Bounds (T a) (C a) (H a) L (K a))
    {D DS E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hA : (Fintype.card A : ℝ) ≤ D)
    (hS : (Fintype.card V : ℝ) ≤ DS) (hperiod : ∀ a, C a ≤ Real.exp E) :
    (Fintype.card (V → ∀ a, ZMod ((e a).period (k a))) : ℝ) ≤ Real.exp (DS * D * E) := by
  simp only [Fintype.card_fun, Nat.cast_pow]
  exact (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _)
    (gridResidueLabels_card_le_exp e k he hE hA hperiod) (mul_nonneg hD hE) _ hS).trans_eq
    (congrArg Real.exp (by ring))

theorem gridResidueRefinement_coefficient_bound [Fintype V]
    {T C H K : A → ℝ} {L : ℝ≥0} (he : ∀ a, (e a).Bounds (T a) (C a) (H a) L (K a))
    {D DS E Ec : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hA : (Fintype.card A : ℝ) ≤ D)
    (hS : (Fintype.card V : ℝ) ≤ DS) (hperiod : ∀ a, C a ≤ Real.exp E)
    {J : Type*} [Fintype J] (c : J → ℂ) (hc : (∑ j, ‖c j‖) ≤ Real.exp Ec) :
    (∑ _r : V → ∀ a, ZMod ((e a).period (k a)), ∑ j, ‖c j‖) ≤ Real.exp (DS * D * E + Ec) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (mul_le_mul (gridSiteResidueLabels_card_le_exp e k he hD hE hA hS hperiod)
    hc (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (radius : ℝ≥0) (hradius : 0 < radius)

include hradius in
theorem allocatedNormalizedGridIdealFactor_residue_product [Fintype V]
    (label : V → ∀ a, ZMod ((e a).period (k a)))
    (f : V → (LayerSamplerAxis I n → ℝ) → ℂ) (y : V → LayerSamplerAxis I n → ℝ) :
    (∏ s, allocatedNormalizedGridIdealFactor B U b S e selected radius hradius k s (label s) (f s) (y s)) =
      ∑ r : V → ∀ a, ZMod ((e a).period (k a)), ∏ s,
        (if label s = r s then (1 : ℂ) else 0) *
          allocatedNormalizedGridIdealFactor B U b S e selected radius hradius k s (r s) (f s) (y s) := by
  exact residueSelectedSiteProduct label (fun r s =>
    allocatedNormalizedGridIdealFactor B U b S e selected radius hradius k s r (f s) (y s))

end Erdos3.VectorPolynomial

end

end OAI
