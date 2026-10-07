import OAI.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {b K M : ℕ} [NeZero M]

theorem exists_weighted_affine_plateau_site_approximation
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin b → NormalizedScalarCubeSource α)
    (u : B → Fin b → Option α → ℤ) (v : B → Fin b → Option α → ℕ)
    (offset : B → ℤ) (p : PMF T) (hK : 0 < K) (H : ℝ)
    (rows : Finset (Finset α)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : F → ℕ, (∀ k, (n k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α F n) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (β : PlateauSiteIndex α F n → ℂ)
        (f : (k : PlateauSiteIndex α F n) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖β k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k u r x, ‖f k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k u r)) ∧
        ∀ y : Finset α → ℤ, (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖(∫ zeta, weightedAffineModeratePlateauApproximation c s u v offset K H rows (shift zeta)
                (fun t => booleanCoefficient y t) F ∂p.toMeasure) -
            ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / K)‖ ≤ δ := by
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have htol : 0 < δ / (C + 1) := div_pos hδ (by positivity)
  obtain ⟨n, hn, hcard, β, f, hβ, hf, hLf, he⟩ :=
    exists_integer_plateau_sum_site_approximation p H K rows (fun k : F => D k)
      (fun k => a k) (fun k => ω k) shift
      (fun k => weightedAffinePlateauModeCoefficient c s u v offset K M rows k)
      (weightedAffinePlateauModeCoefficient_sum_le c s u v offset rows F hscale hcap)
      W (fun k => hW k k.property) hR htol hP hRP hδP hLP
  refine ⟨n, hn, ?_, β, f, hβ, hf, hLf, ?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro y hy
    rw [weightedAffinePlateauModeModel_grid_value c s u v offset p hK H rows F D a ω hfreq shift]
    apply (he y hy).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    nlinarith

end Erdos3

end

end OAI
